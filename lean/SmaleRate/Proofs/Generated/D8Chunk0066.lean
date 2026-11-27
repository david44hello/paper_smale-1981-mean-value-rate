/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1650; no trusted numerical premise.
theorem cover8_leaf1650_exp_radius : (249475791066885451/250000000000000000 : ℝ) ≤ Real.exp ((-2201/131072 : ℝ)/8) ∧ Real.exp ((-2201/131072 : ℝ)/8) ≤ (199580632853508361/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2201/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1650_exp_lower : (230029963831855491/250000000000000000 : ℝ) ≤ Real.exp ((-666010719157/1000000000000 : ℝ)/8) ∧ Real.exp ((-666010719157/1000000000000 : ℝ)/8) ≤ (184023971065484393/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666010719157/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1650_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027508008381/500000000000 : ℝ) ≤ 4*Real.exp (275/2048 : ℝ)*Real.exp (-mu (radius 8 (2201/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027508008381/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2201/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1650_exp_radius
  have hrNumeric : (491673953689/500000000000 : ℝ) ≤ Real.exp (-2201/131072 : ℝ) ∧ Real.exp (-2201/131072 : ℝ) ≤ (983347907379/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491673953689/500000000000 : ℝ) ≤ (radius 8 (2201/16384 : ℝ)) ∧ (radius 8 (2201/16384 : ℝ)) ≤ (983347907379/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2201/16384 : ℝ)) (491673953689/500000000000 : ℝ) (983347907379/1000000000000 : ℝ) (11358314179/62500000000 : ℝ) (18173302687/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2201/16384 : ℝ)) (491673953689/500000000000 : ℝ) (983347907379/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2201/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491673953689/500000000000 : ℝ) (983347907379/1000000000000 : ℝ) (991673953689/1000000000000 : ℝ) (99167395369/100000000000 : ℝ) (247909750133/250000000000 : ℝ) (495819500267/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2201/16384 : ℝ)) 1 (991673953689/1000000000000 : ℝ) (99167395369/100000000000 : ℝ) (247909750133/250000000000 : ℝ) (495819500267/500000000000 : ℝ) (99165647711/100000000000 : ℝ) (123957059639/125000000000 : ℝ) (247914119239/250000000000 : ℝ) (495828238479/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2201/16384 : ℝ)) 2 (99165647711/100000000000 : ℝ) (123957059639/125000000000 : ℝ) (247914119239/250000000000 : ℝ) (495828238479/500000000000 : ℝ) (991656477033/1000000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2201/16384 : ℝ)) 3 (991656477033/1000000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2201/16384 : ℝ)) 4 (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2201/16384 : ℝ)) 5 (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2201/16384 : ℝ)) 6 (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2201/16384 : ℝ)) 7 (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2201/16384 : ℝ))) (11358314179/62500000000 : ℝ) (18173302687/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2201/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11358314179/62500000000 : ℝ) (18173302687/100000000000 : ℝ) (73858314179/125000000000 : ℝ) (118173302687/200000000000 : ℝ) (213150783991/500000000000 : ℝ) (42630156799/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2201/16384 : ℝ))) 1 (73858314179/125000000000 : ℝ) (118173302687/200000000000 : ℝ) (213150783991/500000000000 : ℝ) (42630156799/100000000000 : ℝ) (508584040707/1000000000000 : ℝ) (508584040713/1000000000000 : ℝ) (100376754509/200000000000 : ℝ) (62735471569/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2201/16384 : ℝ))) 2 (508584040707/1000000000000 : ℝ) (508584040713/1000000000000 : ℝ) (100376754509/200000000000 : ℝ) (62735471569/125000000000 : ℝ) (252616953313/500000000000 : ℝ) (505233906633/1000000000000 : ℝ) (126305699843/250000000000 : ℝ) (25261139969/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2201/16384 : ℝ))) 3 (252616953313/500000000000 : ℝ) (505233906633/1000000000000 : ℝ) (126305699843/250000000000 : ℝ) (25261139969/50000000000 : ℝ) (505228352999/1000000000000 : ℝ) (505228353007/1000000000000 : ℝ) (63153544121/125000000000 : ℝ) (31576772061/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2201/16384 : ℝ))) 4 (505228352999/1000000000000 : ℝ) (505228353007/1000000000000 : ℝ) (63153544121/125000000000 : ℝ) (31576772061/62500000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2201/16384 : ℝ))) 5 (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2201/16384 : ℝ))) 6 (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2201/16384 : ℝ))) 7 (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2201/16384 : ℝ)) hmem 8 (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2201/16384 : ℝ))) hcmem 8 (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2201/16384 : ℝ)) (123957059629/125000000000 : ℝ) (198331295407/200000000000 : ℝ) (505228352983/1000000000000 : ℝ) (15788386031/31250000000 : ℝ) (800288062889/1000000000000 : ℝ) (800288062907/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1650_exp_lower
  have heNumeric : (1027508008381/500000000000 : ℝ)/4 ≤ Real.exp (-666010719157/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027508008381/500000000000 : ℝ)/4 ≤ Real.exp ((275/2048 : ℝ)-(800288062907/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (275/2048 : ℝ) (2201/16384 : ℝ) (800288062907/1000000000000 : ℝ) (1027508008381/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1651; no trusted numerical premise.
theorem cover8_leaf1651_exp_radius : (39916088503735103/40000000000000000 : ℝ) ≤ Real.exp ((-1101/65536 : ℝ)/8) ∧ Real.exp ((-1101/65536 : ℝ)/8) ≤ (124737776574172197/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1101/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1651_exp_lower : (460060047206747629/500000000000000000 : ℝ) ≤ Real.exp ((-106561382467/160000000000 : ℝ)/8) ∧ Real.exp ((-106561382467/160000000000 : ℝ)/8) ≤ (920120094413495259/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-106561382467/160000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1651_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055020288607/1000000000000 : ℝ) ≤ 4*Real.exp (2201/16384 : ℝ)*Real.exp (-mu (radius 8 (1101/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2055020288607/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1101/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1651_exp_radius
  have hrNumeric : (491670202529/500000000000 : ℝ) ≤ Real.exp (-1101/65536 : ℝ) ∧ Real.exp (-1101/65536 : ℝ) ≤ (983340405059/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491670202529/500000000000 : ℝ) ≤ (radius 8 (1101/8192 : ℝ)) ∧ (radius 8 (1101/8192 : ℝ)) ≤ (983340405059/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1101/8192 : ℝ)) (491670202529/500000000000 : ℝ) (983340405059/1000000000000 : ℝ) (90886808419/500000000000 : ℝ) (45443404211/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1101/8192 : ℝ)) (491670202529/500000000000 : ℝ) (983340405059/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1101/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491670202529/500000000000 : ℝ) (983340405059/1000000000000 : ℝ) (991670202529/1000000000000 : ℝ) (99167020253/100000000000 : ℝ) (991635217737/1000000000000 : ℝ) (991635217739/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1101/8192 : ℝ)) 1 (991670202529/1000000000000 : ℝ) (99167020253/100000000000 : ℝ) (991635217737/1000000000000 : ℝ) (991635217739/1000000000000 : ℝ) (991652710133/1000000000000 : ℝ) (198330542027/200000000000 : ℝ) (495826354989/500000000000 : ℝ) (991652709981/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1101/8192 : ℝ)) 2 (991652710133/1000000000000 : ℝ) (198330542027/200000000000 : ℝ) (495826354989/500000000000 : ℝ) (991652709981/1000000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1101/8192 : ℝ)) 3 (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1101/8192 : ℝ)) 4 (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1101/8192 : ℝ)) 5 (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1101/8192 : ℝ)) 6 (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1101/8192 : ℝ)) 7 (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1101/8192 : ℝ))) (90886808419/500000000000 : ℝ) (45443404211/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1101/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90886808419/500000000000 : ℝ) (45443404211/250000000000 : ℝ) (590886808419/1000000000000 : ℝ) (295443404211/500000000000 : ℝ) (426349172437/1000000000000 : ℝ) (85269834489/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1101/8192 : ℝ))) 1 (590886808419/1000000000000 : ℝ) (295443404211/500000000000 : ℝ) (426349172437/1000000000000 : ℝ) (85269834489/200000000000 : ℝ) (127154497607/250000000000 : ℝ) (254308995217/500000000000 : ℝ) (62740051723/125000000000 : ℝ) (501920413791/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1101/8192 : ℝ))) 2 (127154497607/250000000000 : ℝ) (254308995217/500000000000 : ℝ) (62740051723/125000000000 : ℝ) (501920413791/1000000000000 : ℝ) (252634601053/500000000000 : ℝ) (505269202113/1000000000000 : ℝ) (10105162091/20000000000 : ℝ) (505258104557/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1101/8192 : ℝ))) 3 (252634601053/500000000000 : ℝ) (505269202113/1000000000000 : ℝ) (10105162091/20000000000 : ℝ) (505258104557/1000000000000 : ℝ) (31578978333/62500000000 : ℝ) (101052730667/200000000000 : ℝ) (505263653297/1000000000000 : ℝ) (101052730661/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1101/8192 : ℝ))) 4 (31578978333/62500000000 : ℝ) (101052730667/200000000000 : ℝ) (505263653297/1000000000000 : ℝ) (101052730661/200000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1101/8192 : ℝ))) 5 (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1101/8192 : ℝ))) 6 (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1101/8192 : ℝ))) 7 (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1101/8192 : ℝ)) hmem 8 (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1101/8192 : ℝ))) hcmem 8 (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1101/8192 : ℝ)) (198330542011/200000000000 : ℝ) (495826355029/500000000000 : ℝ) (7894744583/15625000000 : ℝ) (12631591333/25000000000 : ℝ) (800347019309/1000000000000 : ℝ) (32013880773/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1651_exp_lower
  have heNumeric : (2055020288607/1000000000000 : ℝ)/4 ≤ Real.exp (-106561382467/160000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055020288607/1000000000000 : ℝ)/4 ≤ Real.exp ((2201/16384 : ℝ)-(32013880773/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2201/16384 : ℝ) (1101/8192 : ℝ) (32013880773/40000000000 : ℝ) (2055020288607/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1652; no trusted numerical premise.
theorem cover8_leaf1652_exp_radius : (997900309247771877/1000000000000000000 : ℝ) ≤ Real.exp ((-551/32768 : ℝ)/8) ∧ Real.exp ((-551/32768 : ℝ)/8) ≤ (498950154623885939/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-551/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1652_exp_lower : (460056779443481187/500000000000000000 : ℝ) ≤ Real.exp ((-1332130927737/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332130927737/2000000000000 : ℝ)/8) ≤ (7360908471095699/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332130927737/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1652_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903518583/1000000000000 : ℝ) ≤ 4*Real.exp (1101/8192 : ℝ)*Real.exp (-mu (radius 8 (551/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903518583/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (551/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1652_exp_radius
  have hrNumeric : (245831350147/250000000000 : ℝ) ≤ Real.exp (-551/32768 : ℝ) ∧ Real.exp (-551/32768 : ℝ) ≤ (983325400589/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245831350147/250000000000 : ℝ) ≤ (radius 8 (551/4096 : ℝ)) ∧ (radius 8 (551/4096 : ℝ)) ≤ (983325400589/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (551/4096 : ℝ)) (245831350147/250000000000 : ℝ) (983325400589/1000000000000 : ℝ) (90927383879/500000000000 : ℝ) (45463691941/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (551/4096 : ℝ)) (245831350147/250000000000 : ℝ) (983325400589/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (551/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245831350147/250000000000 : ℝ) (983325400589/1000000000000 : ℝ) (495831350147/500000000000 : ℝ) (198332540059/200000000000 : ℝ) (99162765219/100000000000 : ℝ) (991627652191/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (551/4096 : ℝ)) 1 (495831350147/500000000000 : ℝ) (198332540059/200000000000 : ℝ) (99162765219/100000000000 : ℝ) (991627652191/1000000000000 : ℝ) (495822588121/500000000000 : ℝ) (991645176243/1000000000000 : ℝ) (991645176087/1000000000000 : ℝ) (991645176089/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (551/4096 : ℝ)) 2 (495822588121/500000000000 : ℝ) (991645176243/1000000000000 : ℝ) (991645176087/1000000000000 : ℝ) (991645176089/1000000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (551/4096 : ℝ)) 3 (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (551/4096 : ℝ)) 4 (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (551/4096 : ℝ)) 5 (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (551/4096 : ℝ)) 6 (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (551/4096 : ℝ)) 7 (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (551/4096 : ℝ))) (90927383879/500000000000 : ℝ) (45463691941/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (551/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (90927383879/500000000000 : ℝ) (45463691941/250000000000 : ℝ) (590927383879/1000000000000 : ℝ) (295463691941/500000000000 : ℝ) (42644433137/100000000000 : ℝ) (213222165689/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (551/4096 : ℝ))) 1 (590927383879/1000000000000 : ℝ) (295463691941/500000000000 : ℝ) (42644433137/100000000000 : ℝ) (213222165689/500000000000 : ℝ) (63585732203/125000000000 : ℝ) (50868585763/100000000000 : ℝ) (7843650913/15625000000 : ℝ) (501993658439/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (551/4096 : ℝ))) 2 (63585732203/125000000000 : ℝ) (50868585763/100000000000 : ℝ) (7843650913/15625000000 : ℝ) (501993658439/1000000000000 : ℝ) (126334939507/250000000000 : ℝ) (101067951607/200000000000 : ℝ) (63166084979/125000000000 : ℝ) (3158304249/6250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (551/4096 : ℝ))) 3 (126334939507/250000000000 : ℝ) (101067951607/200000000000 : ℝ) (63166084979/125000000000 : ℝ) (3158304249/6250000000 : ℝ) (50533421893/100000000000 : ℝ) (252667109469/500000000000 : ℝ) (505334218899/1000000000000 : ℝ) (126333554727/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (551/4096 : ℝ))) 4 (50533421893/100000000000 : ℝ) (252667109469/500000000000 : ℝ) (505334218899/1000000000000 : ℝ) (126333554727/250000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (551/4096 : ℝ))) 5 (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (551/4096 : ℝ))) 6 (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (551/4096 : ℝ))) 7 (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (551/4096 : ℝ)) hmem 8 (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (551/4096 : ℝ))) hcmem 8 (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (551/4096 : ℝ)) (247911294041/250000000000 : ℝ) (495822588083/500000000000 : ℝ) (252667109457/500000000000 : ℝ) (505334218923/1000000000000 : ℝ) (400232438957/500000000000 : ℝ) (800464877931/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1652_exp_lower
  have heNumeric : (2054903518583/1000000000000 : ℝ)/4 ≤ Real.exp (-1332130927737/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903518583/1000000000000 : ℝ)/4 ≤ Real.exp ((1101/8192 : ℝ)-(800464877931/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1101/8192 : ℝ) (551/4096 : ℝ) (800464877931/1000000000000 : ℝ) (2054903518583/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1653; no trusted numerical premise.
theorem cover8_leaf1653_exp_radius : (997898405905796519/1000000000000000000 : ℝ) ≤ Real.exp ((-1103/65536 : ℝ)/8) ∧ Real.exp ((-1103/65536 : ℝ)/8) ≤ (24947460147644913/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1103/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1653_exp_lower : (28753564112565527/31250000000000000 : ℝ) ≤ Real.exp ((-666061179919/1000000000000 : ℝ)/8) ∧ Real.exp ((-666061179919/1000000000000 : ℝ)/8) ≤ (184022810320419373/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666061179919/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1653_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256864040213/125000000000 : ℝ) ≤ 4*Real.exp (551/4096 : ℝ)*Real.exp (-mu (radius 8 (1103/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256864040213/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1103/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1653_exp_radius
  have hrNumeric : (245827599087/250000000000 : ℝ) ≤ Real.exp (-1103/65536 : ℝ) ∧ Real.exp (-1103/65536 : ℝ) ≤ (983310396349/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245827599087/250000000000 : ℝ) ≤ (radius 8 (1103/8192 : ℝ)) ∧ (radius 8 (1103/8192 : ℝ)) ≤ (983310396349/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1103/8192 : ℝ)) (245827599087/250000000000 : ℝ) (983310396349/1000000000000 : ℝ) (181935880001/1000000000000 : ℝ) (22741985001/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1103/8192 : ℝ)) (245827599087/250000000000 : ℝ) (983310396349/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1103/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245827599087/250000000000 : ℝ) (983310396349/1000000000000 : ℝ) (495827599087/500000000000 : ℝ) (39666207927/40000000000 : ℝ) (9916200867/10000000000 : ℝ) (495810043351/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1103/8192 : ℝ)) 1 (495827599087/500000000000 : ℝ) (39666207927/40000000000 : ℝ) (9916200867/10000000000 : ℝ) (495810043351/500000000000 : ℝ) (991637642437/1000000000000 : ℝ) (991637642439/1000000000000 : ℝ) (991637642281/1000000000000 : ℝ) (247909410571/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1103/8192 : ℝ)) 2 (991637642437/1000000000000 : ℝ) (991637642439/1000000000000 : ℝ) (991637642281/1000000000000 : ℝ) (247909410571/250000000000 : ℝ) (991637642359/1000000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1103/8192 : ℝ)) 3 (991637642359/1000000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1103/8192 : ℝ)) 4 (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1103/8192 : ℝ)) 5 (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1103/8192 : ℝ)) 6 (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1103/8192 : ℝ)) 7 (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1103/8192 : ℝ))) (181935880001/1000000000000 : ℝ) (22741985001/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1103/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (181935880001/1000000000000 : ℝ) (22741985001/125000000000 : ℝ) (29548397/50000000 : ℝ) (147741985001/250000000000 : ℝ) (85307884747/200000000000 : ℝ) (85307884749/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1103/8192 : ℝ))) 1 (29548397/50000000 : ℝ) (147741985001/250000000000 : ℝ) (85307884747/200000000000 : ℝ) (85307884749/200000000000 : ℝ) (508753681867/1000000000000 : ℝ) (814005891/1600000000 : ℝ) (502066852693/1000000000000 : ℝ) (502066852701/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1103/8192 : ℝ))) 2 (508753681867/1000000000000 : ℝ) (814005891/1600000000 : ℝ) (502066852693/1000000000000 : ℝ) (502066852701/1000000000000 : ℝ) (6317628341/12500000000 : ℝ) (63176283411/125000000000 : ℝ) (505399208399/1000000000000 : ℝ) (63174901051/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1103/8192 : ℝ))) 3 (6317628341/12500000000 : ℝ) (63176283411/125000000000 : ℝ) (505399208399/1000000000000 : ℝ) (63174901051/125000000000 : ℝ) (505404737839/1000000000000 : ℝ) (63175592231/125000000000 : ℝ) (505404737809/1000000000000 : ℝ) (252702368909/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1103/8192 : ℝ))) 4 (505404737839/1000000000000 : ℝ) (63175592231/125000000000 : ℝ) (505404737809/1000000000000 : ℝ) (252702368909/500000000000 : ℝ) (15793898057/31250000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1103/8192 : ℝ))) 5 (15793898057/31250000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1103/8192 : ℝ))) 6 (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1103/8192 : ℝ))) 7 (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1103/8192 : ℝ)) hmem 8 (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1103/8192 : ℝ))) hcmem 8 (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1103/8192 : ℝ)) (495818821179/500000000000 : ℝ) (495818821181/500000000000 : ℝ) (505404737823/1000000000000 : ℝ) (505404737833/1000000000000 : ℝ) (400291332137/500000000000 : ℝ) (400291332147/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1653_exp_lower
  have heNumeric : (256864040213/125000000000 : ℝ)/4 ≤ Real.exp (-666061179919/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256864040213/125000000000 : ℝ)/4 ≤ Real.exp ((551/4096 : ℝ)-(400291332147/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (551/4096 : ℝ) (1103/8192 : ℝ) (400291332147/500000000000 : ℝ) (256864040213/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1654; no trusted numerical premise.
theorem cover8_leaf1654_exp_radius : (498948251283725747/500000000000000000 : ℝ) ≤ Real.exp ((-69/4096 : ℝ)/8) ∧ Real.exp ((-69/4096 : ℝ)/8) ≤ (199579300513490299/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-69/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1654_exp_lower : (460057276305761377/500000000000000000 : ℝ) ≤ Real.exp ((-1332113647713/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332113647713/2000000000000 : ℝ)/8) ≤ (184022910522304551/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332113647713/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1654_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098425461/20000000000 : ℝ) ≤ 4*Real.exp (1103/8192 : ℝ)*Real.exp (-mu (radius 8 (69/512 : ℝ))) ∧ (20549/10000 : ℝ) < (41098425461/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (69/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1654_exp_radius
  have hrNumeric : (61455962021/62500000000 : ℝ) ≤ Real.exp (-69/4096 : ℝ) ∧ Real.exp (-69/4096 : ℝ) ≤ (983295392337/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61455962021/62500000000 : ℝ) ≤ (radius 8 (69/512 : ℝ)) ∧ (radius 8 (69/512 : ℝ)) ≤ (983295392337/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (69/512 : ℝ)) (61455962021/62500000000 : ℝ) (983295392337/1000000000000 : ℝ) (18201695363/100000000000 : ℝ) (45504238409/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (69/512 : ℝ)) (61455962021/62500000000 : ℝ) (983295392337/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (69/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61455962021/62500000000 : ℝ) (983295392337/1000000000000 : ℝ) (123955962021/125000000000 : ℝ) (991647696169/1000000000000 : ℝ) (247903130317/250000000000 : ℝ) (991612521269/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (69/512 : ℝ)) 1 (123955962021/125000000000 : ℝ) (991647696169/1000000000000 : ℝ) (247903130317/250000000000 : ℝ) (991612521269/1000000000000 : ℝ) (495815054359/500000000000 : ℝ) (991630108719/1000000000000 : ℝ) (495815054281/500000000000 : ℝ) (247907527141/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (69/512 : ℝ)) 2 (495815054359/500000000000 : ℝ) (991630108719/1000000000000 : ℝ) (495815054281/500000000000 : ℝ) (247907527141/250000000000 : ℝ) (6197688179/6250000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (69/512 : ℝ)) 3 (6197688179/6250000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (69/512 : ℝ)) 4 (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (69/512 : ℝ)) 5 (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (69/512 : ℝ)) 6 (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (69/512 : ℝ)) 7 (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (69/512 : ℝ))) (18201695363/100000000000 : ℝ) (45504238409/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (69/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (18201695363/100000000000 : ℝ) (45504238409/250000000000 : ℝ) (118201695363/200000000000 : ℝ) (295504238409/500000000000 : ℝ) (106658612413/250000000000 : ℝ) (21331722483/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (69/512 : ℝ))) 1 (118201695363/200000000000 : ℝ) (295504238409/500000000000 : ℝ) (106658612413/250000000000 : ℝ) (21331722483/50000000000 : ℝ) (508821463233/1000000000000 : ℝ) (508821463239/1000000000000 : ℝ) (502139996659/1000000000000 : ℝ) (251069998333/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (69/512 : ℝ))) 2 (508821463233/1000000000000 : ℝ) (508821463239/1000000000000 : ℝ) (502139996659/1000000000000 : ℝ) (251069998333/500000000000 : ℝ) (252740364973/500000000000 : ℝ) (505480729953/1000000000000 : ℝ) (101093938067/200000000000 : ℝ) (252734845171/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (69/512 : ℝ))) 3 (252740364973/500000000000 : ℝ) (505480729953/1000000000000 : ℝ) (101093938067/200000000000 : ℝ) (252734845171/500000000000 : ℝ) (25273760507/50000000000 : ℝ) (126368802537/250000000000 : ℝ) (50547521011/100000000000 : ℝ) (252737605059/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (69/512 : ℝ))) 4 (25273760507/50000000000 : ℝ) (126368802537/250000000000 : ℝ) (50547521011/100000000000 : ℝ) (252737605059/500000000000 : ℝ) (4043801681/8000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (69/512 : ℝ))) 5 (4043801681/8000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (69/512 : ℝ))) 6 (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (69/512 : ℝ))) 7 (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (69/512 : ℝ)) hmem 8 (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (69/512 : ℝ))) hcmem 8 (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (69/512 : ℝ)) (991630108639/1000000000000 : ℝ) (495815054321/500000000000 : ℝ) (126368802531/250000000000 : ℝ) (505475210133/1000000000000 : ℝ) (800700378527/1000000000000 : ℝ) (50043773659/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1654_exp_lower
  have heNumeric : (41098425461/20000000000 : ℝ)/4 ≤ Real.exp (-1332113647713/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098425461/20000000000 : ℝ)/4 ≤ Real.exp ((1103/8192 : ℝ)-(50043773659/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1103/8192 : ℝ) (69/512 : ℝ) (50043773659/62500000000 : ℝ) (41098425461/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1655; no trusted numerical premise.
theorem cover8_leaf1655_exp_radius : (249473649808184199/250000000000000000 : ℝ) ≤ Real.exp ((-1105/65536 : ℝ)/8) ∧ Real.exp ((-1105/65536 : ℝ)/8) ≤ (997894599232736797/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1105/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1655_exp_lower : (115014382737925889/125000000000000000 : ℝ) ≤ Real.exp ((-83256549473/125000000000 : ℝ)/8) ∧ Real.exp ((-83256549473/125000000000 : ℝ)/8) ≤ (920115061903407113/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83256549473/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1655_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054930372411/1000000000000 : ℝ) ≤ 4*Real.exp (69/512 : ℝ)*Real.exp (-mu (radius 8 (1105/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054930372411/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1105/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1655_exp_radius
  have hrNumeric : (491640194277/500000000000 : ℝ) ≤ Real.exp (-1105/65536 : ℝ) ∧ Real.exp (-1105/65536 : ℝ) ≤ (196656077711/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491640194277/500000000000 : ℝ) ≤ (radius 8 (1105/8192 : ℝ)) ∧ (radius 8 (1105/8192 : ℝ)) ≤ (196656077711/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1105/8192 : ℝ)) (491640194277/500000000000 : ℝ) (196656077711/200000000000 : ℝ) (36419597737/200000000000 : ℝ) (182097988691/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1105/8192 : ℝ)) (491640194277/500000000000 : ℝ) (196656077711/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1105/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491640194277/500000000000 : ℝ) (196656077711/200000000000 : ℝ) (991640194277/1000000000000 : ℝ) (495820097139/500000000000 : ℝ) (495802477947/500000000000 : ℝ) (198320991179/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1105/8192 : ℝ)) 1 (991640194277/1000000000000 : ℝ) (495820097139/500000000000 : ℝ) (495802477947/500000000000 : ℝ) (198320991179/200000000000 : ℝ) (198324515017/200000000000 : ℝ) (991622575087/1000000000000 : ℝ) (61976410933/62500000000 : ℝ) (99162257493/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1105/8192 : ℝ)) 2 (198324515017/200000000000 : ℝ) (991622575087/1000000000000 : ℝ) (61976410933/62500000000 : ℝ) (99162257493/100000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1105/8192 : ℝ)) 3 (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1105/8192 : ℝ)) 4 (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1105/8192 : ℝ)) 5 (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1105/8192 : ℝ)) 6 (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1105/8192 : ℝ)) 7 (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1105/8192 : ℝ))) (36419597737/200000000000 : ℝ) (182097988691/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1105/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (36419597737/200000000000 : ℝ) (182097988691/1000000000000 : ℝ) (295524497171/500000000000 : ℝ) (295524497173/500000000000 : ℝ) (42672940921/100000000000 : ℝ) (213364704609/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1105/8192 : ℝ))) 1 (295524497171/500000000000 : ℝ) (295524497173/500000000000 : ℝ) (42672940921/100000000000 : ℝ) (213364704609/500000000000 : ℝ) (31805575111/62500000000 : ℝ) (254444600891/500000000000 : ℝ) (627766363/1250000000 : ℝ) (62776636301/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1105/8192 : ℝ))) 2 (31805575111/62500000000 : ℝ) (254444600891/500000000000 : ℝ) (627766363/1250000000 : ℝ) (62776636301/125000000000 : ℝ) (63193893261/125000000000 : ℝ) (101110229219/200000000000 : ℝ) (252770062851/500000000000 : ℝ) (50554012571/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1105/8192 : ℝ))) 3 (63193893261/125000000000 : ℝ) (101110229219/200000000000 : ℝ) (252770062851/500000000000 : ℝ) (50554012571/100000000000 : ℝ) (101109127179/200000000000 : ℝ) (505545635903/1000000000000 : ℝ) (63193204483/125000000000 : ℝ) (505545635873/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1105/8192 : ℝ))) 4 (101109127179/200000000000 : ℝ) (505545635903/1000000000000 : ℝ) (63193204483/125000000000 : ℝ) (505545635873/1000000000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1105/8192 : ℝ))) 5 (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1105/8192 : ℝ))) 6 (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1105/8192 : ℝ))) 7 (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1105/8192 : ℝ)) hmem 8 (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1105/8192 : ℝ))) hcmem 8 (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1105/8192 : ℝ)) (495811287503/500000000000 : ℝ) (991622575009/1000000000000 : ℝ) (505545635879/1000000000000 : ℝ) (31596602243/62500000000 : ℝ) (400409010383/500000000000 : ℝ) (50051126299/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1655_exp_lower
  have heNumeric : (2054930372411/1000000000000 : ℝ)/4 ≤ Real.exp (-83256549473/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054930372411/1000000000000 : ℝ)/4 ≤ Real.exp ((69/512 : ℝ)-(50051126299/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (69/512 : ℝ) (1105/8192 : ℝ) (50051126299/62500000000 : ℝ) (2054930372411/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1656; no trusted numerical premise.
theorem cover8_leaf1656_exp_radius : (997892695901652417/1000000000000000000 : ℝ) ≤ Real.exp ((-553/32768 : ℝ)/8) ∧ Real.exp ((-553/32768 : ℝ)/8) ≤ (498946347950826209/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-553/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1656_exp_lower : (920115579463731927/1000000000000000000 : ℝ) ≤ Real.exp ((-1332095791647/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332095791647/2000000000000 : ℝ)/8) ≤ (115014447432966491/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332095791647/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1656_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054939619537/1000000000000 : ℝ) ≤ 4*Real.exp (1105/8192 : ℝ)*Real.exp (-mu (radius 8 (553/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054939619537/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (553/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1656_exp_radius
  have hrNumeric : (196653077/200000000 : ℝ) ≤ Real.exp (-553/32768 : ℝ) ∧ Real.exp (-553/32768 : ℝ) ≤ (983265385001/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196653077/200000000 : ℝ) ≤ (radius 8 (553/4096 : ℝ)) ∧ (radius 8 (553/4096 : ℝ)) ≤ (983265385001/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (553/4096 : ℝ)) (196653077/200000000 : ℝ) (983265385001/1000000000000 : ℝ) (45544746307/250000000000 : ℝ) (91089492617/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (553/4096 : ℝ)) (196653077/200000000 : ℝ) (983265385001/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (553/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196653077/200000000 : ℝ) (983265385001/1000000000000 : ℝ) (396653077/400000000 : ℝ) (991632692501/1000000000000 : ℝ) (991597390577/1000000000000 : ℝ) (495798695289/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (553/4096 : ℝ)) 1 (396653077/400000000 : ℝ) (991632692501/1000000000000 : ℝ) (991597390577/1000000000000 : ℝ) (495798695289/500000000000 : ℝ) (495807520769/500000000000 : ℝ) (49580752077/50000000000 : ℝ) (991615041381/1000000000000 : ℝ) (991615041383/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (553/4096 : ℝ)) 2 (495807520769/500000000000 : ℝ) (49580752077/50000000000 : ℝ) (991615041381/1000000000000 : ℝ) (991615041383/1000000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (553/4096 : ℝ)) 3 (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (553/4096 : ℝ)) 4 (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (553/4096 : ℝ)) 5 (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (553/4096 : ℝ)) 6 (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (553/4096 : ℝ)) 7 (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (553/4096 : ℝ))) (45544746307/250000000000 : ℝ) (91089492617/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (553/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (45544746307/250000000000 : ℝ) (91089492617/500000000000 : ℝ) (295544746307/500000000000 : ℝ) (591089492617/1000000000000 : ℝ) (426824302527/1000000000000 : ℝ) (85364860507/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (553/4096 : ℝ))) 1 (295544746307/500000000000 : ℝ) (591089492617/1000000000000 : ℝ) (426824302527/1000000000000 : ℝ) (85364860507/200000000000 : ℝ) (50895689757/100000000000 : ℝ) (63619612197/125000000000 : ℝ) (502286134007/1000000000000 : ℝ) (251143067007/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (553/4096 : ℝ))) 2 (50895689757/100000000000 : ℝ) (63619612197/125000000000 : ℝ) (502286134007/1000000000000 : ℝ) (251143067007/500000000000 : ℝ) (126405378947/250000000000 : ℝ) (101124303159/200000000000 : ℝ) (252805257291/500000000000 : ℝ) (50561051459/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (553/4096 : ℝ))) 3 (126405378947/250000000000 : ℝ) (101124303159/200000000000 : ℝ) (252805257291/500000000000 : ℝ) (50561051459/100000000000 : ℝ) (101123203037/200000000000 : ℝ) (505616015193/1000000000000 : ℝ) (101123203031/200000000000 : ℝ) (505616015163/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (553/4096 : ℝ))) 4 (101123203037/200000000000 : ℝ) (505616015193/1000000000000 : ℝ) (101123203031/200000000000 : ℝ) (505616015163/1000000000000 : ℝ) (50561601517/100000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (553/4096 : ℝ))) 5 (50561601517/100000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (553/4096 : ℝ))) 6 (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (553/4096 : ℝ))) 7 (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (553/4096 : ℝ)) hmem 8 (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (553/4096 : ℝ))) hcmem 8 (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (553/4096 : ℝ)) (991615041459/1000000000000 : ℝ) (495807520731/500000000000 : ℝ) (505616015169/1000000000000 : ℝ) (252808007589/500000000000 : ℝ) (800935591119/1000000000000 : ℝ) (25029237223/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1656_exp_lower
  have heNumeric : (2054939619537/1000000000000 : ℝ)/4 ≤ Real.exp (-1332095791647/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054939619537/1000000000000 : ℝ)/4 ≤ Real.exp ((1105/8192 : ℝ)-(25029237223/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1105/8192 : ℝ) (553/4096 : ℝ) (25029237223/31250000000 : ℝ) (2054939619537/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1657; no trusted numerical premise.
theorem cover8_leaf1657_exp_radius : (19957815851483967/20000000000000000 : ℝ) ≤ Real.exp ((-1107/65536 : ℝ)/8) ∧ Real.exp ((-1107/65536 : ℝ)/8) ≤ (997890792574198351/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1107/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1657_exp_lower : (460058052640159807/500000000000000000 : ℝ) ≤ Real.exp ((-666043324081/1000000000000 : ℝ)/8) ∧ Real.exp ((-666043324081/1000000000000 : ℝ)/8) ≤ (184023221056063923/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666043324081/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1657_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054949014213/1000000000000 : ℝ) ≤ 4*Real.exp (553/4096 : ℝ)*Real.exp (-mu (radius 8 (1107/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054949014213/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1107/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1657_exp_radius
  have hrNumeric : (245812595419/250000000000 : ℝ) ≤ Real.exp (-1107/65536 : ℝ) ∧ Real.exp (-1107/65536 : ℝ) ≤ (983250381677/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245812595419/250000000000 : ℝ) ≤ (radius 8 (1107/8192 : ℝ)) ∧ (radius 8 (1107/8192 : ℝ)) ≤ (983250381677/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1107/8192 : ℝ)) (245812595419/250000000000 : ℝ) (983250381677/1000000000000 : ℝ) (1822599433/10000000000 : ℝ) (182259943307/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1107/8192 : ℝ)) (245812595419/250000000000 : ℝ) (983250381677/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1107/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245812595419/250000000000 : ℝ) (983250381677/1000000000000 : ℝ) (495812595419/500000000000 : ℝ) (991625190839/1000000000000 : ℝ) (495794912659/500000000000 : ℝ) (24789745633/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1107/8192 : ℝ)) 1 (495812595419/500000000000 : ℝ) (991625190839/1000000000000 : ℝ) (495794912659/500000000000 : ℝ) (24789745633/25000000000 : ℝ) (495803754039/500000000000 : ℝ) (12395093851/12500000000 : ℝ) (12395093849/12500000000 : ℝ) (495803753961/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1107/8192 : ℝ)) 2 (495803754039/500000000000 : ℝ) (12395093851/12500000000 : ℝ) (12395093849/12500000000 : ℝ) (495803753961/500000000000 : ℝ) (991607507999/1000000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1107/8192 : ℝ)) 3 (991607507999/1000000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1107/8192 : ℝ)) 4 (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1107/8192 : ℝ)) 5 (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1107/8192 : ℝ)) 6 (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1107/8192 : ℝ)) 7 (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1107/8192 : ℝ))) (1822599433/10000000000 : ℝ) (182259943307/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1107/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1822599433/10000000000 : ℝ) (182259943307/1000000000000 : ℝ) (11822599433/20000000000 : ℝ) (295564985827/500000000000 : ℝ) (85383825939/200000000000 : ℝ) (53364891213/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1107/8192 : ℝ))) 1 (11822599433/20000000000 : ℝ) (295564985827/500000000000 : ℝ) (85383825939/200000000000 : ℝ) (53364891213/125000000000 : ℝ) (31814034417/62500000000 : ℝ) (509024550679/1000000000000 : ℝ) (10047182551/20000000000 : ℝ) (251179563779/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1107/8192 : ℝ))) 2 (31814034417/62500000000 : ℝ) (509024550679/1000000000000 : ℝ) (10047182551/20000000000 : ℝ) (251179563779/500000000000 : ℝ) (505691839111/1000000000000 : ℝ) (505691839119/1000000000000 : ℝ) (6321010713/12500000000 : ℝ) (63210107131/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1107/8192 : ℝ))) 3 (505691839111/1000000000000 : ℝ) (505691839119/1000000000000 : ℝ) (6321010713/12500000000 : ℝ) (63210107131/125000000000 : ℝ) (20227453923/40000000000 : ℝ) (126421587021/250000000000 : ℝ) (101137269609/200000000000 : ℝ) (252843174027/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1107/8192 : ℝ))) 4 (20227453923/40000000000 : ℝ) (126421587021/250000000000 : ℝ) (101137269609/200000000000 : ℝ) (252843174027/500000000000 : ℝ) (25284317403/50000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1107/8192 : ℝ))) 5 (25284317403/50000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1107/8192 : ℝ))) 6 (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1107/8192 : ℝ))) 7 (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1107/8192 : ℝ)) hmem 8 (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1107/8192 : ℝ))) hcmem 8 (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1107/8192 : ℝ)) (495803753999/500000000000 : ℝ) (991607508001/1000000000000 : ℝ) (505686348059/1000000000000 : ℝ) (505686348069/1000000000000 : ℝ) (801053089687/1000000000000 : ℝ) (400526544853/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1657_exp_lower
  have heNumeric : (2054949014213/1000000000000 : ℝ)/4 ≤ Real.exp (-666043324081/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054949014213/1000000000000 : ℝ)/4 ≤ Real.exp ((553/4096 : ℝ)-(400526544853/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (553/4096 : ℝ) (1107/8192 : ℝ) (400526544853/500000000000 : ℝ) (2054949014213/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1658; no trusted numerical premise.
theorem cover8_leaf1658_exp_radius : (997888889250374589/1000000000000000000 : ℝ) ≤ Real.exp ((-277/16384 : ℝ)/8) ∧ Real.exp ((-277/16384 : ℝ)/8) ≤ (99788888925037459/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-277/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1658_exp_lower : (57507289958675469/62500000000000000 : ℝ) ≤ Real.exp ((-1332077361363/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332077361363/2000000000000 : ℝ)/8) ≤ (184023327867761501/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332077361363/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1658_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410991711237/200000000000 : ℝ) ≤ 4*Real.exp (1107/8192 : ℝ)*Real.exp (-mu (radius 8 (277/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (410991711237/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (277/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1658_exp_radius
  have hrNumeric : (49161768929/50000000000 : ℝ) ≤ Real.exp (-277/16384 : ℝ) ∧ Real.exp (-277/16384 : ℝ) ≤ (983235378581/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49161768929/50000000000 : ℝ) ≤ (radius 8 (277/2048 : ℝ)) ∧ (radius 8 (277/2048 : ℝ)) ≤ (983235378581/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (277/2048 : ℝ)) (49161768929/50000000000 : ℝ) (983235378581/1000000000000 : ℝ) (45585215741/250000000000 : ℝ) (18234086297/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (277/2048 : ℝ)) (49161768929/50000000000 : ℝ) (983235378581/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (277/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49161768929/50000000000 : ℝ) (983235378581/1000000000000 : ℝ) (99161768929/100000000000 : ℝ) (991617689291/1000000000000 : ℝ) (991582260117/1000000000000 : ℝ) (991582260119/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (277/2048 : ℝ)) 1 (99161768929/100000000000 : ℝ) (991617689291/1000000000000 : ℝ) (991582260117/1000000000000 : ℝ) (991582260119/1000000000000 : ℝ) (991599974703/1000000000000 : ℝ) (198319994941/200000000000 : ℝ) (198319994909/200000000000 : ℝ) (991599974547/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (277/2048 : ℝ)) 2 (991599974703/1000000000000 : ℝ) (198319994941/200000000000 : ℝ) (198319994909/200000000000 : ℝ) (991599974547/1000000000000 : ℝ) (30987499207/31250000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (277/2048 : ℝ)) 3 (30987499207/31250000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (277/2048 : ℝ)) 4 (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (277/2048 : ℝ)) 5 (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (277/2048 : ℝ)) 6 (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (277/2048 : ℝ)) 7 (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (277/2048 : ℝ))) (45585215741/250000000000 : ℝ) (18234086297/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (277/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (45585215741/250000000000 : ℝ) (18234086297/100000000000 : ℝ) (295585215741/500000000000 : ℝ) (118234086297/200000000000 : ℝ) (26688368177/62500000000 : ℝ) (10675347271/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (277/2048 : ℝ))) 1 (295585215741/500000000000 : ℝ) (118234086297/200000000000 : ℝ) (26688368177/62500000000 : ℝ) (10675347271/25000000000 : ℝ) (509092161157/1000000000000 : ℝ) (509092161163/1000000000000 : ℝ) (251216035561/500000000000 : ℝ) (62804008891/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (277/2048 : ℝ))) 2 (509092161157/1000000000000 : ℝ) (509092161163/1000000000000 : ℝ) (251216035561/500000000000 : ℝ) (62804008891/125000000000 : ℝ) (505762116139/1000000000000 : ℝ) (252881058073/500000000000 : ℝ) (505751153159/1000000000000 : ℝ) (252875576583/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (277/2048 : ℝ))) 3 (505762116139/1000000000000 : ℝ) (252881058073/500000000000 : ℝ) (505751153159/1000000000000 : ℝ) (252875576583/500000000000 : ℝ) (505756634649/1000000000000 : ℝ) (15804894833/31250000000 : ℝ) (505756634619/1000000000000 : ℝ) (505756634627/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (277/2048 : ℝ))) 4 (505756634649/1000000000000 : ℝ) (15804894833/31250000000 : ℝ) (505756634619/1000000000000 : ℝ) (505756634627/1000000000000 : ℝ) (252878317317/500000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (277/2048 : ℝ))) 5 (252878317317/500000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (277/2048 : ℝ))) 6 (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (277/2048 : ℝ))) 7 (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (277/2048 : ℝ)) hmem 8 (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (277/2048 : ℝ))) hcmem 8 (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (277/2048 : ℝ)) (991599974623/1000000000000 : ℝ) (495799987313/500000000000 : ℝ) (505756634633/1000000000000 : ℝ) (252878317321/500000000000 : ℝ) (400585258301/500000000000 : ℝ) (801170516619/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1658_exp_lower
  have heNumeric : (410991711237/200000000000 : ℝ)/4 ≤ Real.exp (-1332077361363/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410991711237/200000000000 : ℝ)/4 ≤ Real.exp ((1107/8192 : ℝ)-(801170516619/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1107/8192 : ℝ) (277/2048 : ℝ) (801170516619/1000000000000 : ℝ) (410991711237/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1659; no trusted numerical premise.
theorem cover8_leaf1659_exp_radius : (997886985930181127/1000000000000000000 : ℝ) ≤ Real.exp ((-1109/65536 : ℝ)/8) ∧ Real.exp ((-1109/65536 : ℝ)/8) ≤ (124735873241272641/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1109/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1659_exp_lower : (460058590813451691/500000000000000000 : ℝ) ≤ Real.exp ((-166508491433/250000000000 : ℝ)/8) ∧ Real.exp ((-166508491433/250000000000 : ℝ)/8) ≤ (920117181626903383/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166508491433/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1659_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054968245233/1000000000000 : ℝ) ≤ 4*Real.exp (277/2048 : ℝ)*Real.exp (-mu (radius 8 (1109/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054968245233/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1109/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1659_exp_radius
  have hrNumeric : (983220375713/1000000000000 : ℝ) ≤ Real.exp (-1109/65536 : ℝ) ∧ Real.exp (-1109/65536 : ℝ) ≤ (491610187857/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983220375713/1000000000000 : ℝ) ≤ (radius 8 (1109/8192 : ℝ)) ∧ (radius 8 (1109/8192 : ℝ)) ≤ (491610187857/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1109/8192 : ℝ)) (983220375713/1000000000000 : ℝ) (491610187857/500000000000 : ℝ) (36484348853/200000000000 : ℝ) (182421744271/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1109/8192 : ℝ)) (983220375713/1000000000000 : ℝ) (491610187857/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1109/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983220375713/1000000000000 : ℝ) (491610187857/500000000000 : ℝ) (61975636741/62500000000 : ℝ) (991610187857/1000000000000 : ℝ) (495787347487/500000000000 : ℝ) (39662987799/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1109/8192 : ℝ)) 1 (61975636741/62500000000 : ℝ) (991610187857/1000000000000 : ℝ) (495787347487/500000000000 : ℝ) (39662987799/40000000000 : ℝ) (198318488283/200000000000 : ℝ) (123949055177/125000000000 : ℝ) (123949055157/125000000000 : ℝ) (495796220629/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1109/8192 : ℝ)) 2 (198318488283/200000000000 : ℝ) (123949055177/125000000000 : ℝ) (123949055157/125000000000 : ℝ) (495796220629/500000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1109/8192 : ℝ)) 3 (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1109/8192 : ℝ)) 4 (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1109/8192 : ℝ)) 5 (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1109/8192 : ℝ)) 6 (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1109/8192 : ℝ)) 7 (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1109/8192 : ℝ))) (36484348853/200000000000 : ℝ) (182421744271/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1109/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (36484348853/200000000000 : ℝ) (182421744271/1000000000000 : ℝ) (147802718033/250000000000 : ℝ) (73901359017/125000000000 : ℝ) (85421717207/200000000000 : ℝ) (427108586043/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1109/8192 : ℝ))) 1 (147802718033/250000000000 : ℝ) (73901359017/125000000000 : ℝ) (85421717207/200000000000 : ℝ) (427108586043/1000000000000 : ℝ) (509159729083/1000000000000 : ℝ) (50915972909/100000000000 : ℝ) (125626241199/250000000000 : ℝ) (502504964803/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1109/8192 : ℝ))) 2 (509159729083/1000000000000 : ℝ) (50915972909/100000000000 : ℝ) (125626241199/250000000000 : ℝ) (502504964803/1000000000000 : ℝ) (505832346939/1000000000000 : ℝ) (505832346947/1000000000000 : ℝ) (101164280601/200000000000 : ℝ) (505821403013/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1109/8192 : ℝ))) 3 (505832346939/1000000000000 : ℝ) (505832346947/1000000000000 : ℝ) (101164280601/200000000000 : ℝ) (505821403013/1000000000000 : ℝ) (126456718743/250000000000 : ℝ) (25291343749/50000000000 : ℝ) (252913437471/500000000000 : ℝ) (505826874951/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1109/8192 : ℝ))) 4 (126456718743/250000000000 : ℝ) (25291343749/50000000000 : ℝ) (252913437471/500000000000 : ℝ) (505826874951/1000000000000 : ℝ) (505826874957/1000000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1109/8192 : ℝ))) 5 (505826874957/1000000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1109/8192 : ℝ))) 6 (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1109/8192 : ℝ))) 7 (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1109/8192 : ℝ)) hmem 8 (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1109/8192 : ℝ))) hcmem 8 (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1109/8192 : ℝ)) (198318488267/200000000000 : ℝ) (991592441337/1000000000000 : ℝ) (126456718739/250000000000 : ℝ) (252913437483/500000000000 : ℝ) (200321967991/250000000000 : ℝ) (400643935991/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1659_exp_lower
  have heNumeric : (2054968245233/1000000000000 : ℝ)/4 ≤ Real.exp (-166508491433/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054968245233/1000000000000 : ℝ)/4 ≤ Real.exp ((277/2048 : ℝ)-(400643935991/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (277/2048 : ℝ) (1109/8192 : ℝ) (400643935991/500000000000 : ℝ) (2054968245233/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1660; no trusted numerical premise.
theorem cover8_leaf1660_exp_radius : (249471270653404489/250000000000000000 : ℝ) ≤ Real.exp ((-555/32768 : ℝ)/8) ∧ Real.exp ((-555/32768 : ℝ)/8) ≤ (997885082613617957/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-555/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1660_exp_lower : (18402354642634803/20000000000000000 : ℝ) ≤ Real.exp ((-1332058358689/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332058358689/2000000000000 : ℝ)/8) ≤ (920117732131740151/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332058358689/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1660_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054978081131/1000000000000 : ℝ) ≤ 4*Real.exp (1109/8192 : ℝ)*Real.exp (-mu (radius 8 (555/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054978081131/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (555/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1660_exp_radius
  have hrNumeric : (39328214923/40000000000 : ℝ) ≤ Real.exp (-555/32768 : ℝ) ∧ Real.exp (-555/32768 : ℝ) ≤ (245801343269/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39328214923/40000000000 : ℝ) ≤ (radius 8 (555/4096 : ℝ)) ∧ (radius 8 (555/4096 : ℝ)) ≤ (245801343269/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (555/4096 : ℝ)) (39328214923/40000000000 : ℝ) (245801343269/250000000000 : ℝ) (91251293627/500000000000 : ℝ) (9125129363/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (555/4096 : ℝ)) (39328214923/40000000000 : ℝ) (245801343269/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (555/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39328214923/40000000000 : ℝ) (245801343269/250000000000 : ℝ) (991602686537/1000000000000 : ℝ) (495801343269/500000000000 : ℝ) (30986472809/31250000000 : ℝ) (991567129889/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (555/4096 : ℝ)) 1 (991602686537/1000000000000 : ℝ) (495801343269/500000000000 : ℝ) (30986472809/31250000000 : ℝ) (991567129889/1000000000000 : ℝ) (247896227053/250000000000 : ℝ) (495792454107/500000000000 : ℝ) (991584908053/1000000000000 : ℝ) (198316981611/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (555/4096 : ℝ)) 2 (247896227053/250000000000 : ℝ) (495792454107/500000000000 : ℝ) (991584908053/1000000000000 : ℝ) (198316981611/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (555/4096 : ℝ)) 3 (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (555/4096 : ℝ)) 4 (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (555/4096 : ℝ)) 5 (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (555/4096 : ℝ)) 6 (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (555/4096 : ℝ)) 7 (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (555/4096 : ℝ))) (91251293627/500000000000 : ℝ) (9125129363/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (555/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (91251293627/500000000000 : ℝ) (9125129363/50000000000 : ℝ) (591251293627/1000000000000 : ℝ) (59125129363/100000000000 : ℝ) (213601607703/500000000000 : ℝ) (213601607707/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (555/4096 : ℝ))) 1 (591251293627/1000000000000 : ℝ) (59125129363/100000000000 : ℝ) (213601607703/500000000000 : ℝ) (213601607707/500000000000 : ℝ) (127306813629/250000000000 : ℝ) (254613627261/500000000000 : ℝ) (125644452163/250000000000 : ℝ) (502577808659/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (555/4096 : ℝ))) 2 (127306813629/250000000000 : ℝ) (254613627261/500000000000 : ℝ) (125644452163/250000000000 : ℝ) (502577808659/1000000000000 : ℝ) (494045441/976562500 : ℝ) (505902531591/1000000000000 : ℝ) (505891606651/1000000000000 : ℝ) (505891606659/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (555/4096 : ℝ))) 3 (494045441/976562500 : ℝ) (505902531591/1000000000000 : ℝ) (505891606651/1000000000000 : ℝ) (505891606659/1000000000000 : ℝ) (505897069117/1000000000000 : ℝ) (4047176553/8000000000 : ℝ) (15809283409/31250000000 : ℝ) (63237133637/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (555/4096 : ℝ))) 4 (505897069117/1000000000000 : ℝ) (4047176553/8000000000 : ℝ) (15809283409/31250000000 : ℝ) (63237133637/125000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (555/4096 : ℝ))) 5 (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (555/4096 : ℝ))) 6 (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (555/4096 : ℝ))) 7 (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (555/4096 : ℝ)) hmem 8 (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (555/4096 : ℝ))) hcmem 8 (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (555/4096 : ℝ)) (247896227033/250000000000 : ℝ) (198316981627/200000000000 : ℝ) (252948534551/500000000000 : ℝ) (505897069111/1000000000000 : ℝ) (801405155889/1000000000000 : ℝ) (801405155907/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1660_exp_lower
  have heNumeric : (2054978081131/1000000000000 : ℝ)/4 ≤ Real.exp (-1332058358689/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054978081131/1000000000000 : ℝ)/4 ≤ Real.exp ((1109/8192 : ℝ)-(801405155907/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1109/8192 : ℝ) (555/4096 : ℝ) (801405155907/1000000000000 : ℝ) (2054978081131/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1661; no trusted numerical premise.
theorem cover8_leaf1661_exp_radius : (997883179300685071/1000000000000000000 : ℝ) ≤ Real.exp ((-1111/65536 : ℝ)/8) ∧ Real.exp ((-1111/65536 : ℝ)/8) ≤ (62367698706292817/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1111/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1661_exp_lower : (920118290839990839/1000000000000000000 : ℝ) ≤ Real.exp ((-133204864327/200000000000 : ℝ)/8) ∧ Real.exp ((-133204864327/200000000000 : ℝ)/8) ≤ (23002957270999771/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133204864327/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1661_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027494031821/500000000000 : ℝ) ≤ 4*Real.exp (555/4096 : ℝ)*Real.exp (-mu (radius 8 (1111/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027494031821/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1111/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1661_exp_radius
  have hrNumeric : (491595185333/500000000000 : ℝ) ≤ Real.exp (-1111/65536 : ℝ) ∧ Real.exp (-1111/65536 : ℝ) ≤ (983190370667/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491595185333/500000000000 : ℝ) ≤ (radius 8 (1111/8192 : ℝ)) ∧ (radius 8 (1111/8192 : ℝ)) ≤ (983190370667/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1111/8192 : ℝ)) (491595185333/500000000000 : ℝ) (983190370667/1000000000000 : ℝ) (91291695991/500000000000 : ℝ) (45645847997/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1111/8192 : ℝ)) (491595185333/500000000000 : ℝ) (983190370667/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1111/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491595185333/500000000000 : ℝ) (983190370667/1000000000000 : ℝ) (991595185333/1000000000000 : ℝ) (495797592667/500000000000 : ℝ) (49577978243/50000000000 : ℝ) (991559564861/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1111/8192 : ℝ)) 1 (991595185333/1000000000000 : ℝ) (495797592667/500000000000 : ℝ) (49577978243/50000000000 : ℝ) (991559564861/1000000000000 : ℝ) (123947171887/125000000000 : ℝ) (495788687549/500000000000 : ℝ) (123947171867/125000000000 : ℝ) (495788687469/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1111/8192 : ℝ)) 2 (123947171887/125000000000 : ℝ) (495788687549/500000000000 : ℝ) (123947171867/125000000000 : ℝ) (495788687469/500000000000 : ℝ) (123947171877/125000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1111/8192 : ℝ)) 3 (123947171877/125000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1111/8192 : ℝ)) 4 (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1111/8192 : ℝ)) 5 (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1111/8192 : ℝ)) 6 (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1111/8192 : ℝ)) 7 (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1111/8192 : ℝ))) (91291695991/500000000000 : ℝ) (45645847997/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1111/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (91291695991/500000000000 : ℝ) (45645847997/250000000000 : ℝ) (591291695991/1000000000000 : ℝ) (295645847997/500000000000 : ℝ) (427297779051/1000000000000 : ℝ) (427297779059/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1111/8192 : ℝ))) 1 (591291695991/1000000000000 : ℝ) (295645847997/500000000000 : ℝ) (427297779051/1000000000000 : ℝ) (427297779059/1000000000000 : ℝ) (509294737521/1000000000000 : ℝ) (509294737527/1000000000000 : ℝ) (502650602773/1000000000000 : ℝ) (25132530139/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1111/8192 : ℝ))) 2 (509294737521/1000000000000 : ℝ) (509294737527/1000000000000 : ℝ) (502650602773/1000000000000 : ℝ) (25132530139/50000000000 : ℝ) (505972670147/1000000000000 : ℝ) (252986335077/500000000000 : ℝ) (126490441043/250000000000 : ℝ) (505961764179/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1111/8192 : ℝ))) 3 (505972670147/1000000000000 : ℝ) (252986335077/500000000000 : ℝ) (126490441043/250000000000 : ℝ) (505961764179/1000000000000 : ℝ) (505967217159/1000000000000 : ℝ) (505967217167/1000000000000 : ℝ) (50596721713/100000000000 : ℝ) (252983608569/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1111/8192 : ℝ))) 4 (505967217159/1000000000000 : ℝ) (505967217167/1000000000000 : ℝ) (50596721713/100000000000 : ℝ) (252983608569/500000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1111/8192 : ℝ))) 5 (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1111/8192 : ℝ))) 6 (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1111/8192 : ℝ))) 7 (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1111/8192 : ℝ)) hmem 8 (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1111/8192 : ℝ))) hcmem 8 (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1111/8192 : ℝ)) (198315475003/200000000000 : ℝ) (495788687509/500000000000 : ℝ) (63245902143/125000000000 : ℝ) (505967217153/1000000000000 : ℝ) (200380592123/250000000000 : ℝ) (80152236851/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1661_exp_lower
  have heNumeric : (1027494031821/500000000000 : ℝ)/4 ≤ Real.exp (-133204864327/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027494031821/500000000000 : ℝ)/4 ≤ Real.exp ((555/4096 : ℝ)-(80152236851/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (555/4096 : ℝ) (1111/8192 : ℝ) (80152236851/100000000000 : ℝ) (1027494031821/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1662; no trusted numerical premise.
theorem cover8_leaf1662_exp_radius : (997881275991382463/1000000000000000000 : ℝ) ≤ Real.exp ((-139/8192 : ℝ)/8) ∧ Real.exp ((-139/8192 : ℝ)/8) ≤ (15591894937365351/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-139/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1662_exp_lower : (230029714434840951/250000000000000000 : ℝ) ≤ Real.exp ((-1332038785421/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332038785421/2000000000000 : ℝ)/8) ≤ (184023771547872761/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332038785421/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1662_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513749548137/250000000000 : ℝ) ≤ 4*Real.exp (1111/8192 : ℝ)*Real.exp (-mu (radius 8 (139/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (513749548137/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (139/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1662_exp_radius
  have hrNumeric : (491587684243/500000000000 : ℝ) ≤ Real.exp (-139/8192 : ℝ) ∧ Real.exp (-139/8192 : ℝ) ≤ (983175368487/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491587684243/500000000000 : ℝ) ≤ (radius 8 (139/1024 : ℝ)) ∧ (radius 8 (139/1024 : ℝ)) ≤ (983175368487/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (139/1024 : ℝ)) (491587684243/500000000000 : ℝ) (983175368487/1000000000000 : ℝ) (182664158499/1000000000000 : ℝ) (91332079253/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (139/1024 : ℝ)) (491587684243/500000000000 : ℝ) (983175368487/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (139/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491587684243/500000000000 : ℝ) (983175368487/1000000000000 : ℝ) (991587684243/1000000000000 : ℝ) (247896921061/250000000000 : ℝ) (99155199989/100000000000 : ℝ) (991551999891/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (139/1024 : ℝ)) 1 (991587684243/1000000000000 : ℝ) (247896921061/250000000000 : ℝ) (99155199989/100000000000 : ℝ) (991551999891/1000000000000 : ℝ) (495784921033/500000000000 : ℝ) (247892460517/250000000000 : ℝ) (198313968381/200000000000 : ℝ) (991569841907/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (139/1024 : ℝ)) 2 (495784921033/500000000000 : ℝ) (247892460517/250000000000 : ℝ) (198313968381/200000000000 : ℝ) (991569841907/1000000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (139/1024 : ℝ)) 3 (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (139/1024 : ℝ)) 4 (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (139/1024 : ℝ)) 5 (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (139/1024 : ℝ)) 6 (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (139/1024 : ℝ)) 7 (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (139/1024 : ℝ))) (182664158499/1000000000000 : ℝ) (91332079253/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (139/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (182664158499/1000000000000 : ℝ) (91332079253/500000000000 : ℝ) (591332079249/1000000000000 : ℝ) (591332079253/1000000000000 : ℝ) (427392277069/1000000000000 : ℝ) (427392277079/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (139/1024 : ℝ))) 1 (591332079249/1000000000000 : ℝ) (591332079253/1000000000000 : ℝ) (427392277069/1000000000000 : ℝ) (427392277079/1000000000000 : ℝ) (509362178159/1000000000000 : ℝ) (254681089083/500000000000 : ℝ) (251361673617/500000000000 : ℝ) (251361673621/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (139/1024 : ℝ))) 2 (509362178159/1000000000000 : ℝ) (254681089083/500000000000 : ℝ) (251361673617/500000000000 : ℝ) (251361673621/500000000000 : ℝ) (63255345337/125000000000 : ℝ) (31627672669/62500000000 : ℝ) (253015937817/500000000000 : ℝ) (506031875643/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (139/1024 : ℝ))) 3 (63255345337/125000000000 : ℝ) (31627672669/62500000000 : ℝ) (253015937817/500000000000 : ℝ) (506031875643/1000000000000 : ℝ) (101207463833/200000000000 : ℝ) (253018659587/500000000000 : ℝ) (101207463827/200000000000 : ℝ) (101207463829/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (139/1024 : ℝ))) 4 (101207463833/200000000000 : ℝ) (253018659587/500000000000 : ℝ) (101207463827/200000000000 : ℝ) (101207463829/200000000000 : ℝ) (10120746383/20000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (139/1024 : ℝ))) 5 (10120746383/20000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (139/1024 : ℝ))) 6 (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (139/1024 : ℝ))) 7 (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (139/1024 : ℝ)) hmem 8 (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (139/1024 : ℝ))) hcmem 8 (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (139/1024 : ℝ)) (198313968397/200000000000 : ℝ) (247892460497/250000000000 : ℝ) (506037319149/1000000000000 : ℝ) (12650932979/25000000000 : ℝ) (801639509877/1000000000000 : ℝ) (400819754949/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1662_exp_lower
  have heNumeric : (513749548137/250000000000 : ℝ)/4 ≤ Real.exp (-1332038785421/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513749548137/250000000000 : ℝ)/4 ≤ Real.exp ((1111/8192 : ℝ)-(400819754949/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1111/8192 : ℝ) (139/1024 : ℝ) (400819754949/500000000000 : ℝ) (513749548137/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1663; no trusted numerical premise.
theorem cover8_leaf1663_exp_radius : (498939686342855063/500000000000000000 : ℝ) ≤ Real.exp ((-1113/65536 : ℝ)/8) ∧ Real.exp ((-1113/65536 : ℝ)/8) ≤ (997879372685710127/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1113/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1663_exp_lower : (920119432816762483/1000000000000000000 : ℝ) ≤ Real.exp ((-133202878537/200000000000 : ℝ)/8) ∧ Real.exp ((-133202878537/200000000000 : ℝ)/8) ≤ (230029858204190621/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133202878537/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1663_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055008467617/1000000000000 : ℝ) ≤ 4*Real.exp (139/1024 : ℝ)*Real.exp (-mu (radius 8 (1113/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2055008467617/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1113/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1663_exp_radius
  have hrNumeric : (196632073307/200000000000 : ℝ) ≤ Real.exp (-1113/65536 : ℝ) ∧ Real.exp (-1113/65536 : ℝ) ≤ (122895045817/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196632073307/200000000000 : ℝ) ≤ (radius 8 (1113/8192 : ℝ)) ∧ (radius 8 (1113/8192 : ℝ)) ≤ (122895045817/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1113/8192 : ℝ)) (196632073307/200000000000 : ℝ) (122895045817/125000000000 : ℝ) (91372443429/500000000000 : ℝ) (11421555429/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1113/8192 : ℝ)) (196632073307/200000000000 : ℝ) (122895045817/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1113/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196632073307/200000000000 : ℝ) (122895045817/125000000000 : ℝ) (991580183267/1000000000000 : ℝ) (247895045817/250000000000 : ℝ) (991544434977/1000000000000 : ℝ) (991544434979/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1113/8192 : ℝ)) 1 (991580183267/1000000000000 : ℝ) (247895045817/250000000000 : ℝ) (991544434977/1000000000000 : ℝ) (991544434979/1000000000000 : ℝ) (495781154561/500000000000 : ℝ) (247890577281/250000000000 : ℝ) (6197264431/6250000000 : ℝ) (991562308963/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1113/8192 : ℝ)) 2 (495781154561/500000000000 : ℝ) (247890577281/250000000000 : ℝ) (6197264431/6250000000 : ℝ) (991562308963/1000000000000 : ℝ) (991562309041/1000000000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1113/8192 : ℝ)) 3 (991562309041/1000000000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1113/8192 : ℝ)) 4 (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1113/8192 : ℝ)) 5 (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1113/8192 : ℝ)) 6 (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1113/8192 : ℝ)) 7 (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1113/8192 : ℝ))) (91372443429/500000000000 : ℝ) (11421555429/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1113/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (91372443429/500000000000 : ℝ) (11421555429/62500000000 : ℝ) (591372443429/1000000000000 : ℝ) (73921555429/125000000000 : ℝ) (6679479837/15625000000 : ℝ) (53435838697/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1113/8192 : ℝ))) 1 (591372443429/1000000000000 : ℝ) (73921555429/125000000000 : ℝ) (6679479837/15625000000 : ℝ) (53435838697/125000000000 : ℝ) (254714788249/500000000000 : ℝ) (63678697063/125000000000 : ℝ) (502796042119/1000000000000 : ℝ) (251398021063/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1113/8192 : ℝ))) 2 (254714788249/500000000000 : ℝ) (63678697063/125000000000 : ℝ) (502796042119/1000000000000 : ℝ) (251398021063/500000000000 : ℝ) (126528202327/250000000000 : ℝ) (101222561863/200000000000 : ℝ) (126525485279/250000000000 : ℝ) (506101941123/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1113/8192 : ℝ))) 3 (126528202327/250000000000 : ℝ) (101222561863/200000000000 : ℝ) (126525485279/250000000000 : ℝ) (506101941123/1000000000000 : ℝ) (126526843803/250000000000 : ℝ) (506107375219/1000000000000 : ℝ) (253053687591/500000000000 : ℝ) (50610737519/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1113/8192 : ℝ))) 4 (126526843803/250000000000 : ℝ) (506107375219/1000000000000 : ℝ) (253053687591/500000000000 : ℝ) (50610737519/100000000000 : ℝ) (506107375197/1000000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1113/8192 : ℝ))) 5 (506107375197/1000000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1113/8192 : ℝ))) 6 (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1113/8192 : ℝ))) 7 (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1113/8192 : ℝ)) hmem 8 (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1113/8192 : ℝ))) hcmem 8 (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1113/8192 : ℝ)) (12394528863/12500000000 : ℝ) (247890577261/250000000000 : ℝ) (126526843799/250000000000 : ℝ) (101221475041/200000000000 : ℝ) (801756580167/1000000000000 : ℝ) (160351316037/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1663_exp_lower
  have heNumeric : (2055008467617/1000000000000 : ℝ)/4 ≤ Real.exp (-133202878537/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055008467617/1000000000000 : ℝ)/4 ≤ Real.exp ((139/1024 : ℝ)-(160351316037/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (139/1024 : ℝ) (1113/8192 : ℝ) (160351316037/200000000000 : ℝ) (2055008467617/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1664; no trusted numerical premise.
theorem cover8_leaf1664_exp_radius : (997877469383668053/1000000000000000000 : ℝ) ≤ Real.exp ((-557/32768 : ℝ)/8) ∧ Real.exp ((-557/32768 : ℝ)/8) ≤ (498938734691834027/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-557/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1664_exp_lower : (920120016058745453/1000000000000000000 : ℝ) ≤ Real.exp ((-1332018643351/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332018643351/2000000000000 : ℝ)/8) ≤ (460060008029372727/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332018643351/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1664_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055018888611/1000000000000 : ℝ) ≤ 4*Real.exp (1113/8192 : ℝ)*Real.exp (-mu (radius 8 (557/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2055018888611/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (557/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1664_exp_radius
  have hrNumeric : (983145364813/1000000000000 : ℝ) ≤ Real.exp (-557/32768 : ℝ) ∧ Real.exp (-557/32768 : ℝ) ≤ (491572682407/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983145364813/1000000000000 : ℝ) ≤ (radius 8 (557/4096 : ℝ)) ∧ (radius 8 (557/4096 : ℝ)) ≤ (491572682407/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (557/4096 : ℝ)) (983145364813/1000000000000 : ℝ) (491572682407/500000000000 : ℝ) (182825577107/1000000000000 : ℝ) (91412788557/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (557/4096 : ℝ)) (983145364813/1000000000000 : ℝ) (491572682407/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (557/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983145364813/1000000000000 : ℝ) (491572682407/500000000000 : ℝ) (495786341203/500000000000 : ℝ) (991572682407/1000000000000 : ℝ) (495768435061/500000000000 : ℝ) (247884217531/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (557/4096 : ℝ)) 1 (495786341203/500000000000 : ℝ) (991572682407/1000000000000 : ℝ) (495768435061/500000000000 : ℝ) (247884217531/250000000000 : ℝ) (123944347033/125000000000 : ℝ) (495777388133/500000000000 : ℝ) (495777388051/500000000000 : ℝ) (123944347013/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (557/4096 : ℝ)) 2 (123944347033/125000000000 : ℝ) (495777388133/500000000000 : ℝ) (495777388051/500000000000 : ℝ) (123944347013/125000000000 : ℝ) (991554776183/1000000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (557/4096 : ℝ)) 3 (991554776183/1000000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (557/4096 : ℝ)) 4 (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (557/4096 : ℝ)) 5 (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (557/4096 : ℝ)) 6 (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (557/4096 : ℝ)) 7 (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (557/4096 : ℝ))) (182825577107/1000000000000 : ℝ) (91412788557/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (557/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (182825577107/1000000000000 : ℝ) (91412788557/500000000000 : ℝ) (591412788553/1000000000000 : ℝ) (591412788557/1000000000000 : ℝ) (427581076647/1000000000000 : ℝ) (26723817291/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (557/4096 : ℝ))) 1 (591412788553/1000000000000 : ℝ) (591412788557/1000000000000 : ℝ) (427581076647/1000000000000 : ℝ) (26723817291/62500000000 : ℝ) (2547484663/5000000000 : ℝ) (509496932607/1000000000000 : ℝ) (31429292969/62500000000 : ℝ) (62858585939/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (557/4096 : ℝ))) 2 (2547484663/5000000000 : ℝ) (509496932607/1000000000000 : ℝ) (31429292969/62500000000 : ℝ) (62858585939/125000000000 : ℝ) (126545702513/250000000000 : ℝ) (25309140503/50000000000 : ℝ) (101234392137/200000000000 : ℝ) (506171960693/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (557/4096 : ℝ))) 3 (126545702513/250000000000 : ℝ) (25309140503/50000000000 : ℝ) (101234392137/200000000000 : ℝ) (506171960693/1000000000000 : ℝ) (63272173171/125000000000 : ℝ) (506177385377/1000000000000 : ℝ) (506177385339/1000000000000 : ℝ) (126544346337/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (557/4096 : ℝ))) 4 (63272173171/125000000000 : ℝ) (506177385377/1000000000000 : ℝ) (506177385339/1000000000000 : ℝ) (126544346337/250000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (557/4096 : ℝ))) 5 (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (557/4096 : ℝ))) 6 (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (557/4096 : ℝ))) 7 (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (557/4096 : ℝ)) hmem 8 (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (557/4096 : ℝ))) hcmem 8 (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (557/4096 : ℝ)) (495777388091/500000000000 : ℝ) (198310955237/200000000000 : ℝ) (506177385353/1000000000000 : ℝ) (506177385363/1000000000000 : ℝ) (801873579469/1000000000000 : ℝ) (25058549359/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1664_exp_lower
  have heNumeric : (2055018888611/1000000000000 : ℝ)/4 ≤ Real.exp (-1332018643351/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055018888611/1000000000000 : ℝ)/4 ≤ Real.exp ((1113/8192 : ℝ)-(25058549359/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1113/8192 : ℝ) (557/4096 : ℝ) (25058549359/31250000000 : ℝ) (2055018888611/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1665; no trusted numerical premise.
theorem cover8_leaf1665_exp_radius : (997875566085256237/1000000000000000000 : ℝ) ≤ Real.exp ((-1115/65536 : ℝ)/8) ∧ Real.exp ((-1115/65536 : ℝ)/8) ≤ (498937783042628119/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1115/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1665_exp_lower : (57507537965835417/62500000000000000 : ℝ) ≤ Real.exp ((-333002089893/500000000000 : ℝ)/8) ∧ Real.exp ((-333002089893/500000000000 : ℝ)/8) ≤ (920120607453366673/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333002089893/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1665_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027514727659/500000000000 : ℝ) ≤ 4*Real.exp (557/4096 : ℝ)*Real.exp (-mu (radius 8 (1115/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027514727659/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1115/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1665_exp_radius
  have hrNumeric : (24578259083/25000000000 : ℝ) ≤ Real.exp (-1115/65536 : ℝ) ∧ Real.exp (-1115/65536 : ℝ) ≤ (983130363321/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24578259083/25000000000 : ℝ) ≤ (radius 8 (1115/8192 : ℝ)) ∧ (radius 8 (1115/8192 : ℝ)) ≤ (983130363321/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1115/8192 : ℝ)) (24578259083/25000000000 : ℝ) (983130363321/1000000000000 : ℝ) (91453114649/500000000000 : ℝ) (36581245861/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1115/8192 : ℝ)) (24578259083/25000000000 : ℝ) (983130363321/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1115/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24578259083/25000000000 : ℝ) (983130363321/1000000000000 : ℝ) (49578259083/50000000000 : ℝ) (991565181661/1000000000000 : ℝ) (39661172213/40000000000 : ℝ) (991529305327/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1115/8192 : ℝ)) 1 (49578259083/50000000000 : ℝ) (991565181661/1000000000000 : ℝ) (39661172213/40000000000 : ℝ) (991529305327/1000000000000 : ℝ) (247886810873/250000000000 : ℝ) (495773621747/500000000000 : ℝ) (99154724333/100000000000 : ℝ) (247886810833/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1115/8192 : ℝ)) 2 (247886810873/250000000000 : ℝ) (495773621747/500000000000 : ℝ) (99154724333/100000000000 : ℝ) (247886810833/250000000000 : ℝ) (991547243411/1000000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1115/8192 : ℝ)) 3 (991547243411/1000000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1115/8192 : ℝ)) 4 (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1115/8192 : ℝ)) 5 (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1115/8192 : ℝ)) 6 (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1115/8192 : ℝ)) 7 (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1115/8192 : ℝ))) (91453114649/500000000000 : ℝ) (36581245861/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1115/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (91453114649/500000000000 : ℝ) (36581245861/200000000000 : ℝ) (591453114649/1000000000000 : ℝ) (591453114653/1000000000000 : ℝ) (427675378409/1000000000000 : ℝ) (427675378419/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1115/8192 : ℝ))) 1 (591453114649/1000000000000 : ℝ) (591453114653/1000000000000 : ℝ) (427675378409/1000000000000 : ℝ) (427675378419/1000000000000 : ℝ) (509564246529/1000000000000 : ℝ) (63695530817/125000000000 : ℝ) (50294128347/100000000000 : ℝ) (251470641739/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1115/8192 : ℝ))) 2 (509564246529/1000000000000 : ℝ) (63695530817/125000000000 : ℝ) (50294128347/100000000000 : ℝ) (251470641739/500000000000 : ℝ) (506252764999/1000000000000 : ℝ) (506252765007/1000000000000 : ℝ) (253120967207/500000000000 : ℝ) (253120967211/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1115/8192 : ℝ))) 3 (506252764999/1000000000000 : ℝ) (506252765007/1000000000000 : ℝ) (253120967207/500000000000 : ℝ) (253120967211/500000000000 : ℝ) (253123674853/500000000000 : ℝ) (101249469943/200000000000 : ℝ) (506247349677/1000000000000 : ℝ) (253123674843/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1115/8192 : ℝ))) 4 (253123674853/500000000000 : ℝ) (101249469943/200000000000 : ℝ) (506247349677/1000000000000 : ℝ) (253123674843/500000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1115/8192 : ℝ))) 5 (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1115/8192 : ℝ))) 6 (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1115/8192 : ℝ))) 7 (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1115/8192 : ℝ)) hmem 8 (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1115/8192 : ℝ))) hcmem 8 (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1115/8192 : ℝ)) (99154724341/100000000000 : ℝ) (991547243413/1000000000000 : ℝ) (506247349691/1000000000000 : ℝ) (506247349701/1000000000000 : ℝ) (200497626973/250000000000 : ℝ) (801990507911/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1665_exp_lower
  have heNumeric : (1027514727659/500000000000 : ℝ)/4 ≤ Real.exp (-333002089893/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027514727659/500000000000 : ℝ)/4 ≤ Real.exp ((557/4096 : ℝ)-(801990507911/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (557/4096 : ℝ) (1115/8192 : ℝ) (801990507911/1000000000000 : ℝ) (1027514727659/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1666; no trusted numerical premise.
theorem cover8_leaf1666_exp_radius : (997873662790474671/1000000000000000000 : ℝ) ≤ Real.exp ((-279/16384 : ℝ)/8) ∧ Real.exp ((-279/16384 : ℝ)/8) ≤ (62367103924404667/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-279/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1666_exp_lower : (920121206986494997/1000000000000000000 : ℝ) ≤ Real.exp ((-1331997934279/2000000000000 : ℝ)/8) ∧ Real.exp ((-1331997934279/2000000000000 : ℝ)/8) ≤ (460060603493247499/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1331997934279/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1666_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (32110002617/15625000000 : ℝ) ≤ 4*Real.exp (1115/8192 : ℝ)*Real.exp (-mu (radius 8 (279/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (32110002617/15625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (279/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1666_exp_radius
  have hrNumeric : (196623072411/200000000000 : ℝ) ≤ Real.exp (-279/16384 : ℝ) ∧ Real.exp (-279/16384 : ℝ) ≤ (122889420257/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196623072411/200000000000 : ℝ) ≤ (radius 8 (279/2048 : ℝ)) ∧ (radius 8 (279/2048 : ℝ)) ≤ (122889420257/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (279/2048 : ℝ)) (196623072411/200000000000 : ℝ) (122889420257/125000000000 : ℝ) (182986843487/1000000000000 : ℝ) (182986843493/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (279/2048 : ℝ)) (196623072411/200000000000 : ℝ) (122889420257/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (279/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196623072411/200000000000 : ℝ) (122889420257/125000000000 : ℝ) (991557681027/1000000000000 : ℝ) (247889420257/250000000000 : ℝ) (495760870293/500000000000 : ℝ) (991521740587/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (279/2048 : ℝ)) 1 (991557681027/1000000000000 : ℝ) (247889420257/250000000000 : ℝ) (495760870293/500000000000 : ℝ) (991521740587/1000000000000 : ℝ) (495769855403/500000000000 : ℝ) (123942463851/125000000000 : ℝ) (991539710643/1000000000000 : ℝ) (198307942129/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (279/2048 : ℝ)) 2 (495769855403/500000000000 : ℝ) (123942463851/125000000000 : ℝ) (991539710643/1000000000000 : ℝ) (198307942129/200000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (279/2048 : ℝ)) 3 (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (279/2048 : ℝ)) 4 (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (279/2048 : ℝ)) 5 (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (279/2048 : ℝ)) 6 (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (279/2048 : ℝ)) 7 (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (279/2048 : ℝ))) (182986843487/1000000000000 : ℝ) (182986843493/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (279/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (182986843487/1000000000000 : ℝ) (182986843493/1000000000000 : ℝ) (591493421743/1000000000000 : ℝ) (591493421747/1000000000000 : ℝ) (106942403741/250000000000 : ℝ) (106942403743/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (279/2048 : ℝ))) 1 (591493421743/1000000000000 : ℝ) (591493421747/1000000000000 : ℝ) (106942403741/250000000000 : ℝ) (106942403743/250000000000 : ℝ) (509631518353/1000000000000 : ℝ) (12740787959/25000000000 : ℝ) (5030138301/10000000000 : ℝ) (125753457527/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (279/2048 : ℝ))) 2 (509631518353/1000000000000 : ℝ) (12740787959/25000000000 : ℝ) (5030138301/10000000000 : ℝ) (125753457527/250000000000 : ℝ) (253161337113/500000000000 : ℝ) (253161337117/500000000000 : ℝ) (506311862379/1000000000000 : ℝ) (126577965597/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (279/2048 : ℝ))) 3 (253161337113/500000000000 : ℝ) (253161337117/500000000000 : ℝ) (506311862379/1000000000000 : ℝ) (126577965597/250000000000 : ℝ) (253158634151/500000000000 : ℝ) (506317268311/1000000000000 : ℝ) (506317268273/1000000000000 : ℝ) (506317268283/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (279/2048 : ℝ))) 4 (253158634151/500000000000 : ℝ) (506317268311/1000000000000 : ℝ) (506317268273/1000000000000 : ℝ) (506317268283/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (279/2048 : ℝ))) 5 (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (279/2048 : ℝ))) 6 (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (279/2048 : ℝ))) 7 (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (279/2048 : ℝ)) hmem 8 (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (279/2048 : ℝ))) hcmem 8 (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (279/2048 : ℝ)) (247884927681/250000000000 : ℝ) (991539710727/1000000000000 : ℝ) (506317268287/1000000000000 : ℝ) (506317268297/1000000000000 : ℝ) (401053682779/500000000000 : ℝ) (802107365577/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1666_exp_lower
  have heNumeric : (32110002617/15625000000 : ℝ)/4 ≤ Real.exp (-1331997934279/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (32110002617/15625000000 : ℝ)/4 ≤ Real.exp ((1115/8192 : ℝ)-(802107365577/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1115/8192 : ℝ) (279/2048 : ℝ) (802107365577/1000000000000 : ℝ) (32110002617/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1667; no trusted numerical premise.
theorem cover8_leaf1667_exp_radius : (249467939874830837/250000000000000000 : ℝ) ≤ Real.exp ((-1117/65536 : ℝ)/8) ∧ Real.exp ((-1117/65536 : ℝ)/8) ≤ (997871759499323349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1117/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1667_exp_lower : (920121814646874843/1000000000000000000 : ℝ) ≤ Real.exp ((-332996841917/500000000000 : ℝ)/8) ∧ Real.exp ((-332996841917/500000000000 : ℝ)/8) ≤ (230030453661718711/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332996841917/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1667_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027525512461/500000000000 : ℝ) ≤ 4*Real.exp (279/2048 : ℝ)*Real.exp (-mu (radius 8 (1117/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027525512461/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1117/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1667_exp_radius
  have hrNumeric : (49155018051/50000000000 : ℝ) ≤ Real.exp (-1117/65536 : ℝ) ∧ Real.exp (-1117/65536 : ℝ) ≤ (983100361021/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49155018051/50000000000 : ℝ) ≤ (radius 8 (1117/8192 : ℝ)) ∧ (radius 8 (1117/8192 : ℝ)) ≤ (983100361021/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1117/8192 : ℝ)) (49155018051/50000000000 : ℝ) (983100361021/1000000000000 : ℝ) (183067419713/1000000000000 : ℝ) (183067419719/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1117/8192 : ℝ)) (49155018051/50000000000 : ℝ) (983100361021/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1117/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49155018051/50000000000 : ℝ) (983100361021/1000000000000 : ℝ) (99155018051/100000000000 : ℝ) (991550180511/1000000000000 : ℝ) (30984817997/31250000000 : ℝ) (495757087953/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1117/8192 : ℝ)) 1 (99155018051/100000000000 : ℝ) (991550180511/1000000000000 : ℝ) (30984817997/31250000000 : ℝ) (495757087953/500000000000 : ℝ) (991532178207/1000000000000 : ℝ) (991532178209/1000000000000 : ℝ) (991532178043/1000000000000 : ℝ) (495766089023/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1117/8192 : ℝ)) 2 (991532178207/1000000000000 : ℝ) (991532178209/1000000000000 : ℝ) (991532178043/1000000000000 : ℝ) (495766089023/500000000000 : ℝ) (317290297/320000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1117/8192 : ℝ)) 3 (317290297/320000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1117/8192 : ℝ)) 4 (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1117/8192 : ℝ)) 5 (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1117/8192 : ℝ)) 6 (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1117/8192 : ℝ)) 7 (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1117/8192 : ℝ))) (183067419713/1000000000000 : ℝ) (183067419719/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1117/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (183067419713/1000000000000 : ℝ) (183067419719/1000000000000 : ℝ) (18485428433/31250000000 : ℝ) (29576685493/50000000000 : ℝ) (534829733/1250000000 : ℝ) (53482973301/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1117/8192 : ℝ))) 1 (18485428433/31250000000 : ℝ) (29576685493/50000000000 : ℝ) (534829733/1250000000 : ℝ) (53482973301/125000000000 : ℝ) (15928085879/31250000000 : ℝ) (254849374067/500000000000 : ℝ) (100617265493/200000000000 : ℝ) (31442895467/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1117/8192 : ℝ))) 2 (15928085879/31250000000 : ℝ) (254849374067/500000000000 : ℝ) (100617265493/200000000000 : ℝ) (31442895467/62500000000 : ℝ) (126598134449/250000000000 : ℝ) (506392537803/1000000000000 : ℝ) (126595436161/250000000000 : ℝ) (126595436163/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1117/8192 : ℝ))) 3 (126598134449/250000000000 : ℝ) (506392537803/1000000000000 : ℝ) (126595436161/250000000000 : ℝ) (126595436163/250000000000 : ℝ) (25319357061/50000000000 : ℝ) (126596785307/250000000000 : ℝ) (506387141191/1000000000000 : ℝ) (506387141199/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1117/8192 : ℝ))) 4 (25319357061/50000000000 : ℝ) (126596785307/250000000000 : ℝ) (506387141191/1000000000000 : ℝ) (506387141199/1000000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1117/8192 : ℝ))) 5 (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1117/8192 : ℝ))) 6 (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1117/8192 : ℝ))) 7 (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1117/8192 : ℝ)) hmem 8 (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1117/8192 : ℝ))) hcmem 8 (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1117/8192 : ℝ)) (247883044531/250000000000 : ℝ) (61970761133/62500000000 : ℝ) (101277428241/200000000000 : ℝ) (253193570607/500000000000 : ℝ) (401112076283/500000000000 : ℝ) (100278019073/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1667_exp_lower
  have heNumeric : (1027525512461/500000000000 : ℝ)/4 ≤ Real.exp (-332996841917/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027525512461/500000000000 : ℝ)/4 ≤ Real.exp ((279/2048 : ℝ)-(100278019073/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (279/2048 : ℝ) (1117/8192 : ℝ) (100278019073/125000000000 : ℝ) (1027525512461/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1668; no trusted numerical premise.
theorem cover8_leaf1668_exp_radius : (498934928105901131/500000000000000000 : ℝ) ≤ Real.exp ((-559/32768 : ℝ)/8) ∧ Real.exp ((-559/32768 : ℝ)/8) ≤ (997869856211802263/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-559/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1668_exp_lower : (36804897216828819/40000000000000000 : ℝ) ≤ Real.exp ((-1331976659979/2000000000000 : ℝ)/8) ∧ Real.exp ((-1331976659979/2000000000000 : ℝ)/8) ≤ (230030607605180119/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1331976659979/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1668_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16440496219/8000000000 : ℝ) ≤ 4*Real.exp (1117/8192 : ℝ)*Real.exp (-mu (radius 8 (559/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (16440496219/8000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (559/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1668_exp_radius
  have hrNumeric : (983085360213/1000000000000 : ℝ) ≤ Real.exp (-559/32768 : ℝ) ∧ Real.exp (-559/32768 : ℝ) ≤ (491542680107/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983085360213/1000000000000 : ℝ) ≤ (radius 8 (559/4096 : ℝ)) ∧ (radius 8 (559/4096 : ℝ)) ≤ (491542680107/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (559/4096 : ℝ)) (983085360213/1000000000000 : ℝ) (491542680107/500000000000 : ℝ) (45786989509/250000000000 : ℝ) (91573979021/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (559/4096 : ℝ)) (983085360213/1000000000000 : ℝ) (491542680107/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (559/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983085360213/1000000000000 : ℝ) (491542680107/500000000000 : ℝ) (495771340053/500000000000 : ℝ) (991542680107/1000000000000 : ℝ) (12393832641/12500000000 : ℝ) (495753305641/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (559/4096 : ℝ)) 1 (495771340053/500000000000 : ℝ) (991542680107/1000000000000 : ℝ) (12393832641/12500000000 : ℝ) (495753305641/500000000000 : ℝ) (991524645693/1000000000000 : ℝ) (198304929139/200000000000 : ℝ) (123940580691/125000000000 : ℝ) (991524645531/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (559/4096 : ℝ)) 2 (991524645693/1000000000000 : ℝ) (198304929139/200000000000 : ℝ) (123940580691/125000000000 : ℝ) (991524645531/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (559/4096 : ℝ)) 3 (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (559/4096 : ℝ)) 4 (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (559/4096 : ℝ)) 5 (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (559/4096 : ℝ)) 6 (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (559/4096 : ℝ)) 7 (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (559/4096 : ℝ))) (45786989509/250000000000 : ℝ) (91573979021/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (559/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (45786989509/250000000000 : ℝ) (91573979021/500000000000 : ℝ) (295786989509/500000000000 : ℝ) (591573979021/1000000000000 : ℝ) (42795789283/100000000000 : ℝ) (213978946419/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (559/4096 : ℝ))) 1 (295786989509/500000000000 : ℝ) (591573979021/1000000000000 : ℝ) (42795789283/100000000000 : ℝ) (213978946419/500000000000 : ℝ) (127441483981/250000000000 : ℝ) (50976593593/100000000000 : ℝ) (503158775649/1000000000000 : ℝ) (62894846957/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (559/4096 : ℝ))) 2 (127441483981/250000000000 : ℝ) (50976593593/100000000000 : ℝ) (503158775649/1000000000000 : ℝ) (62894846957/125000000000 : ℝ) (253231177893/500000000000 : ℝ) (506462355793/1000000000000 : ℝ) (101290316257/200000000000 : ℝ) (506451581293/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (559/4096 : ℝ))) 3 (253231177893/500000000000 : ℝ) (506462355793/1000000000000 : ℝ) (101290316257/200000000000 : ℝ) (506451581293/1000000000000 : ℝ) (101291393707/200000000000 : ℝ) (506456968543/1000000000000 : ℝ) (253228484253/500000000000 : ℝ) (101291393703/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (559/4096 : ℝ))) 4 (101291393707/200000000000 : ℝ) (506456968543/1000000000000 : ℝ) (253228484253/500000000000 : ℝ) (101291393703/200000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (559/4096 : ℝ))) 5 (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (559/4096 : ℝ))) 6 (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (559/4096 : ℝ))) 7 (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (559/4096 : ℝ)) hmem 8 (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (559/4096 : ℝ))) hcmem 8 (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (559/4096 : ℝ)) (99152464561/100000000000 : ℝ) (991524645613/1000000000000 : ℝ) (12661424213/25000000000 : ℝ) (506456968529/1000000000000 : ℝ) (160468173807/200000000000 : ℝ) (200585217263/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1668_exp_lower
  have heNumeric : (16440496219/8000000000 : ℝ)/4 ≤ Real.exp (-1331976659979/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16440496219/8000000000 : ℝ)/4 ≤ Real.exp ((1117/8192 : ℝ)-(200585217263/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1117/8192 : ℝ) (559/4096 : ℝ) (200585217263/250000000000 : ℝ) (16440496219/8000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1669; no trusted numerical premise.
theorem cover8_leaf1669_exp_radius : (199573590585582281/200000000000000000 : ℝ) ≤ Real.exp ((-1119/65536 : ℝ)/8) ∧ Real.exp ((-1119/65536 : ℝ)/8) ≤ (498933976463955703/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1119/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1669_exp_lower : (920123054296201597/1000000000000000000 : ℝ) ≤ Real.exp ((-665982905709/1000000000000 : ℝ)/8) ∧ Real.exp ((-665982905709/1000000000000 : ℝ)/8) ≤ (460061527148100799/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665982905709/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1669_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027536587319/500000000000 : ℝ) ≤ 4*Real.exp (559/4096 : ℝ)*Real.exp (-mu (radius 8 (1119/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027536587319/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1119/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1669_exp_radius
  have hrNumeric : (245767589909/250000000000 : ℝ) ≤ Real.exp (-1119/65536 : ℝ) ∧ Real.exp (-1119/65536 : ℝ) ≤ (983070359637/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245767589909/250000000000 : ℝ) ≤ (radius 8 (1119/8192 : ℝ)) ∧ (radius 8 (1119/8192 : ℝ)) ≤ (983070359637/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1119/8192 : ℝ)) (245767589909/250000000000 : ℝ) (983070359637/1000000000000 : ℝ) (357868083/1953125000 : ℝ) (183228458503/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1119/8192 : ℝ)) (245767589909/250000000000 : ℝ) (983070359637/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1119/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245767589909/250000000000 : ℝ) (983070359637/1000000000000 : ℝ) (495767589909/500000000000 : ℝ) (991535179819/1000000000000 : ℝ) (495749523357/500000000000 : ℝ) (247874761679/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1119/8192 : ℝ)) 1 (495767589909/500000000000 : ℝ) (991535179819/1000000000000 : ℝ) (495749523357/500000000000 : ℝ) (247874761679/250000000000 : ℝ) (495758556633/500000000000 : ℝ) (247879278317/250000000000 : ℝ) (991517113101/1000000000000 : ℝ) (991517113103/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1119/8192 : ℝ)) 2 (495758556633/500000000000 : ℝ) (247879278317/250000000000 : ℝ) (991517113101/1000000000000 : ℝ) (991517113103/1000000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1119/8192 : ℝ)) 3 (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1119/8192 : ℝ)) 4 (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1119/8192 : ℝ)) 5 (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1119/8192 : ℝ)) 6 (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1119/8192 : ℝ)) 7 (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1119/8192 : ℝ))) (357868083/1953125000 : ℝ) (183228458503/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1119/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (357868083/1953125000 : ℝ) (183228458503/1000000000000 : ℝ) (2310993083/3906250000 : ℝ) (147903557313/250000000000 : ℝ) (53506491793/125000000000 : ℝ) (428051934353/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1119/8192 : ℝ))) 1 (2310993083/3906250000 : ℝ) (147903557313/250000000000 : ℝ) (53506491793/125000000000 : ℝ) (428051934353/1000000000000 : ℝ) (127458270449/250000000000 : ℝ) (509833081803/1000000000000 : ℝ) (125807793681/250000000000 : ℝ) (125807793683/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1119/8192 : ℝ))) 2 (127458270449/250000000000 : ℝ) (509833081803/1000000000000 : ℝ) (125807793681/250000000000 : ℝ) (125807793683/250000000000 : ℝ) (25326606413/50000000000 : ℝ) (126633032067/250000000000 : ℝ) (506521372367/1000000000000 : ℝ) (63315171547/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1119/8192 : ℝ))) 3 (25326606413/50000000000 : ℝ) (126633032067/250000000000 : ℝ) (506521372367/1000000000000 : ℝ) (63315171547/125000000000 : ℝ) (506526750313/1000000000000 : ℝ) (253263375161/500000000000 : ℝ) (126631687571/250000000000 : ℝ) (253263375147/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1119/8192 : ℝ))) 4 (506526750313/1000000000000 : ℝ) (253263375161/500000000000 : ℝ) (126631687571/250000000000 : ℝ) (253263375147/500000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1119/8192 : ℝ))) 5 (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1119/8192 : ℝ))) 6 (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1119/8192 : ℝ))) 7 (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1119/8192 : ℝ)) hmem 8 (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1119/8192 : ℝ))) hcmem 8 (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1119/8192 : ℝ)) (991517113183/1000000000000 : ℝ) (495758556593/500000000000 : ℝ) (253263375149/500000000000 : ℝ) (126631687577/250000000000 : ℝ) (100307189383/125000000000 : ℝ) (200614378771/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1669_exp_lower
  have heNumeric : (1027536587319/500000000000 : ℝ)/4 ≤ Real.exp (-665982905709/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027536587319/500000000000 : ℝ)/4 ≤ Real.exp ((559/4096 : ℝ)-(200614378771/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (559/4096 : ℝ) (1119/8192 : ℝ) (200614378771/250000000000 : ℝ) (1027536587319/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1670; no trusted numerical premise.
theorem cover8_leaf1670_exp_radius : (997866049647650771/1000000000000000000 : ℝ) ≤ Real.exp ((-35/2048 : ℝ)/8) ∧ Real.exp ((-35/2048 : ℝ)/8) ≤ (249466512411912693/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-35/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1670_exp_lower : (920123686259417819/1000000000000000000 : ℝ) ≤ Real.exp ((-1331954822227/2000000000000 : ℝ)/8) ∧ Real.exp ((-1331954822227/2000000000000 : ℝ)/8) ≤ (46006184312970891/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1331954822227/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1670_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (411016893293/200000000000 : ℝ) ≤ 4*Real.exp (1119/8192 : ℝ)*Real.exp (-mu (radius 8 (35/256 : ℝ))) ∧ (20549/10000 : ℝ) < (411016893293/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (35/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1670_exp_radius
  have hrNumeric : (983055359287/1000000000000 : ℝ) ≤ Real.exp (-35/2048 : ℝ) ∧ Real.exp (-35/2048 : ℝ) ≤ (122881919911/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983055359287/1000000000000 : ℝ) ≤ (radius 8 (35/256 : ℝ)) ∧ (radius 8 (35/256 : ℝ)) ≤ (122881919911/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (35/256 : ℝ)) (983055359287/1000000000000 : ℝ) (122881919911/125000000000 : ℝ) (36661784231/200000000000 : ℝ) (183308921161/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (35/256 : ℝ)) (983055359287/1000000000000 : ℝ) (122881919911/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (35/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983055359287/1000000000000 : ℝ) (122881919911/125000000000 : ℝ) (991527679643/1000000000000 : ℝ) (247881919911/250000000000 : ℝ) (198298296441/200000000000 : ℝ) (991491482207/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (35/256 : ℝ)) 1 (991527679643/1000000000000 : ℝ) (247881919911/250000000000 : ℝ) (198298296441/200000000000 : ℝ) (991491482207/1000000000000 : ℝ) (247877395231/250000000000 : ℝ) (495754790463/500000000000 : ℝ) (495754790379/500000000000 : ℝ) (991509580761/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (35/256 : ℝ)) 2 (247877395231/250000000000 : ℝ) (495754790463/500000000000 : ℝ) (495754790379/500000000000 : ℝ) (991509580761/1000000000000 : ℝ) (991509580841/1000000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (35/256 : ℝ)) 3 (991509580841/1000000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (35/256 : ℝ)) 4 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (35/256 : ℝ)) 5 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (35/256 : ℝ)) 6 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (35/256 : ℝ)) 7 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (35/256 : ℝ))) (36661784231/200000000000 : ℝ) (183308921161/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (35/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (36661784231/200000000000 : ℝ) (183308921161/1000000000000 : ℝ) (591654460577/1000000000000 : ℝ) (591654460581/1000000000000 : ℝ) (428145911057/1000000000000 : ℝ) (85629182213/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (35/256 : ℝ))) 1 (591654460577/1000000000000 : ℝ) (591654460581/1000000000000 : ℝ) (428145911057/1000000000000 : ℝ) (85629182213/200000000000 : ℝ) (509900185817/1000000000000 : ℝ) (509900185823/1000000000000 : ℝ) (251651762389/500000000000 : ℝ) (251651762393/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (35/256 : ℝ))) 2 (509900185817/1000000000000 : ℝ) (509900185823/1000000000000 : ℝ) (251651762389/500000000000 : ℝ) (251651762393/500000000000 : ℝ) (506601855297/1000000000000 : ℝ) (101320371061/200000000000 : ℝ) (50659111797/100000000000 : ℝ) (253295558989/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (35/256 : ℝ))) 3 (506601855297/1000000000000 : ℝ) (101320371061/200000000000 : ℝ) (50659111797/100000000000 : ℝ) (253295558989/500000000000 : ℝ) (506596486633/1000000000000 : ℝ) (253298243321/500000000000 : ℝ) (101319297321/200000000000 : ℝ) (253298243307/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (35/256 : ℝ))) 4 (506596486633/1000000000000 : ℝ) (253298243321/500000000000 : ℝ) (101319297321/200000000000 : ℝ) (253298243307/500000000000 : ℝ) (506596486619/1000000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (35/256 : ℝ))) 5 (506596486619/1000000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (35/256 : ℝ))) 6 (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (35/256 : ℝ))) 7 (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (35/256 : ℝ)) hmem 8 (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (35/256 : ℝ))) hcmem 8 (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (35/256 : ℝ)) (24787739521/25000000000 : ℝ) (247877395211/250000000000 : ℝ) (253298243309/500000000000 : ℝ) (126649121657/250000000000 : ℝ) (802574090781/1000000000000 : ℝ) (802574090801/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1670_exp_lower
  have heNumeric : (411016893293/200000000000 : ℝ)/4 ≤ Real.exp (-1331954822227/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (411016893293/200000000000 : ℝ)/4 ≤ Real.exp ((1119/8192 : ℝ)-(802574090801/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1119/8192 : ℝ) (35/256 : ℝ) (802574090801/1000000000000 : ℝ) (411016893293/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1671; no trusted numerical premise.
theorem cover8_leaf1671_exp_radius : (15591627287047193/15625000000000000 : ℝ) ≤ Real.exp ((-1121/65536 : ℝ)/8) ∧ Real.exp ((-1121/65536 : ℝ)/8) ≤ (997864146371020353/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1121/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1671_exp_lower : (184024865259799853/200000000000000000 : ℝ) ≤ Real.exp ((-332985923151/500000000000 : ℝ)/8) ∧ Real.exp ((-332985923151/500000000000 : ℝ)/8) ≤ (460062163149499633/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332985923151/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1671_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027547951327/500000000000 : ℝ) ≤ 4*Real.exp (35/256 : ℝ)*Real.exp (-mu (radius 8 (1121/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027547951327/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1121/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1671_exp_radius
  have hrNumeric : (983040359167/1000000000000 : ℝ) ≤ Real.exp (-1121/65536 : ℝ) ∧ Real.exp (-1121/65536 : ℝ) ≤ (3840001403/3906250000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983040359167/1000000000000 : ℝ) ≤ (radius 8 (1121/8192 : ℝ)) ∧ (radius 8 (1121/8192 : ℝ)) ≤ (3840001403/3906250000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1121/8192 : ℝ)) (983040359167/1000000000000 : ℝ) (3840001403/3906250000 : ℝ) (22923668257/125000000000 : ℝ) (91694673031/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1121/8192 : ℝ)) (983040359167/1000000000000 : ℝ) (3840001403/3906250000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1121/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983040359167/1000000000000 : ℝ) (3840001403/3906250000 : ℝ) (991520179583/1000000000000 : ℝ) (7746251403/7812500000 : ℝ) (198296783551/200000000000 : ℝ) (247870979439/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1121/8192 : ℝ)) 1 (991520179583/1000000000000 : ℝ) (7746251403/7812500000 : ℝ) (198296783551/200000000000 : ℝ) (247870979439/250000000000 : ℝ) (991502048669/1000000000000 : ℝ) (99150204867/100000000000 : ℝ) (991502048503/1000000000000 : ℝ) (198300409701/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1121/8192 : ℝ)) 2 (991502048669/1000000000000 : ℝ) (99150204867/100000000000 : ℝ) (991502048503/1000000000000 : ℝ) (198300409701/200000000000 : ℝ) (495751024293/500000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1121/8192 : ℝ)) 3 (495751024293/500000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1121/8192 : ℝ)) 4 (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1121/8192 : ℝ)) 5 (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1121/8192 : ℝ)) 6 (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1121/8192 : ℝ)) 7 (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1121/8192 : ℝ))) (22923668257/125000000000 : ℝ) (91694673031/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1121/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22923668257/125000000000 : ℝ) (91694673031/500000000000 : ℝ) (147923668257/250000000000 : ℝ) (591694673031/1000000000000 : ℝ) (428239823061/1000000000000 : ℝ) (428239823069/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1121/8192 : ℝ))) 1 (147923668257/250000000000 : ℝ) (591694673031/1000000000000 : ℝ) (428239823061/1000000000000 : ℝ) (428239823069/1000000000000 : ℝ) (127491812011/250000000000 : ℝ) (10199344961/20000000000 : ℝ) (503375825883/1000000000000 : ℝ) (50337582589/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1121/8192 : ℝ))) 2 (127491812011/250000000000 : ℝ) (10199344961/20000000000 : ℝ) (503375825883/1000000000000 : ℝ) (50337582589/100000000000 : ℝ) (506671536963/1000000000000 : ℝ) (50667153697/100000000000 : ℝ) (253330409079/500000000000 : ℝ) (253330409083/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1121/8192 : ℝ))) 3 (506671536963/1000000000000 : ℝ) (50667153697/100000000000 : ℝ) (253330409079/500000000000 : ℝ) (253330409083/500000000000 : ℝ) (12666654439/25000000000 : ℝ) (15833318049/31250000000 : ℝ) (126666544383/250000000000 : ℝ) (25333308877/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1121/8192 : ℝ))) 4 (12666654439/25000000000 : ℝ) (15833318049/31250000000 : ℝ) (126666544383/250000000000 : ℝ) (25333308877/50000000000 : ℝ) (253333088773/500000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1121/8192 : ℝ))) 5 (253333088773/500000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1121/8192 : ℝ))) 6 (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1121/8192 : ℝ))) 7 (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1121/8192 : ℝ)) hmem 8 (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1121/8192 : ℝ))) hcmem 8 (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1121/8192 : ℝ)) (198300409717/200000000000 : ℝ) (247875512147/250000000000 : ℝ) (101333235509/200000000000 : ℝ) (253333088777/500000000000 : ℝ) (200672649071/250000000000 : ℝ) (401345298151/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1671_exp_lower
  have heNumeric : (1027547951327/500000000000 : ℝ)/4 ≤ Real.exp (-332985923151/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027547951327/500000000000 : ℝ)/4 ≤ Real.exp ((35/256 : ℝ)-(401345298151/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (35/256 : ℝ) (1121/8192 : ℝ) (401345298151/500000000000 : ℝ) (1027547951327/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1672; no trusted numerical premise.
theorem cover8_leaf1672_exp_radius : (498931121549010071/500000000000000000 : ℝ) ≤ Real.exp ((-561/32768 : ℝ)/8) ∧ Real.exp ((-561/32768 : ℝ)/8) ≤ (997862243098020143/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-561/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1672_exp_lower : (57507810900101311/62500000000000000 : ℝ) ≤ Real.exp ((-1331932422781/2000000000000 : ℝ)/8) ∧ Real.exp ((-1331932422781/2000000000000 : ℝ)/8) ≤ (920124974401620977/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1331932422781/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1672_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055107482971/1000000000000 : ℝ) ≤ 4*Real.exp (1121/8192 : ℝ)*Real.exp (-mu (radius 8 (561/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2055107482971/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (561/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1672_exp_radius
  have hrNumeric : (245756339819/250000000000 : ℝ) ≤ Real.exp (-561/32768 : ℝ) ∧ Real.exp (-561/32768 : ℝ) ≤ (983025359277/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245756339819/250000000000 : ℝ) ≤ (radius 8 (561/4096 : ℝ)) ∧ (radius 8 (561/4096 : ℝ)) ≤ (983025359277/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (561/4096 : ℝ)) (245756339819/250000000000 : ℝ) (983025359277/1000000000000 : ℝ) (1433357291/7812500000 : ℝ) (91734866627/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (561/4096 : ℝ)) (245756339819/250000000000 : ℝ) (983025359277/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (561/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245756339819/250000000000 : ℝ) (983025359277/1000000000000 : ℝ) (495756339819/500000000000 : ℝ) (991512679639/1000000000000 : ℝ) (991476353361/1000000000000 : ℝ) (991476353363/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (561/4096 : ℝ)) 1 (495756339819/500000000000 : ℝ) (991512679639/1000000000000 : ℝ) (991476353361/1000000000000 : ℝ) (991476353363/1000000000000 : ℝ) (991494516499/1000000000000 : ℝ) (991494516501/1000000000000 : ℝ) (991494516333/1000000000000 : ℝ) (198298903267/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (561/4096 : ℝ)) 2 (991494516499/1000000000000 : ℝ) (991494516501/1000000000000 : ℝ) (991494516333/1000000000000 : ℝ) (198298903267/200000000000 : ℝ) (15492101819/15625000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (561/4096 : ℝ)) 3 (15492101819/15625000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (561/4096 : ℝ)) 4 (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (561/4096 : ℝ)) 5 (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (561/4096 : ℝ)) 6 (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (561/4096 : ℝ)) 7 (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (561/4096 : ℝ))) (1433357291/7812500000 : ℝ) (91734866627/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (561/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1433357291/7812500000 : ℝ) (91734866627/500000000000 : ℝ) (9245857291/15625000000 : ℝ) (591734866627/1000000000000 : ℝ) (428333670457/1000000000000 : ℝ) (85666734093/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (561/4096 : ℝ))) 1 (9245857291/15625000000 : ℝ) (591734866627/1000000000000 : ℝ) (428333670457/1000000000000 : ℝ) (85666734093/200000000000 : ℝ) (25501713427/50000000000 : ℝ) (255017134273/500000000000 : ℝ) (100689615623/200000000000 : ℝ) (251724039061/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (561/4096 : ℝ))) 2 (25501713427/50000000000 : ℝ) (255017134273/500000000000 : ℝ) (100689615623/200000000000 : ℝ) (251724039061/500000000000 : ℝ) (506741173327/1000000000000 : ℝ) (253370586667/500000000000 : ℝ) (253365236501/500000000000 : ℝ) (506730473009/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (561/4096 : ℝ))) 3 (506741173327/1000000000000 : ℝ) (253370586667/500000000000 : ℝ) (253365236501/500000000000 : ℝ) (506730473009/1000000000000 : ℝ) (126683955791/250000000000 : ℝ) (126683955793/250000000000 : ℝ) (15835494473/31250000000 : ℝ) (63341977893/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (561/4096 : ℝ))) 4 (126683955791/250000000000 : ℝ) (126683955793/250000000000 : ℝ) (15835494473/31250000000 : ℝ) (63341977893/125000000000 : ℝ) (10134716463/20000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (561/4096 : ℝ))) 5 (10134716463/20000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (561/4096 : ℝ))) 6 (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (561/4096 : ℝ))) 7 (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (561/4096 : ℝ)) hmem 8 (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (561/4096 : ℝ))) hcmem 8 (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (561/4096 : ℝ)) (198298903283/200000000000 : ℝ) (495747258209/500000000000 : ℝ) (506735823149/1000000000000 : ℝ) (253367911579/500000000000 : ℝ) (160561406337/200000000000 : ℝ) (802807031703/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1672_exp_lower
  have heNumeric : (2055107482971/1000000000000 : ℝ)/4 ≤ Real.exp (-1331932422781/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055107482971/1000000000000 : ℝ)/4 ≤ Real.exp ((1121/8192 : ℝ)-(802807031703/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1121/8192 : ℝ) (561/4096 : ℝ) (802807031703/1000000000000 : ℝ) (2055107482971/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1673; no trusted numerical premise.
theorem cover8_leaf1673_exp_radius : (997860339828650133/1000000000000000000 : ℝ) ≤ Real.exp ((-1123/65536 : ℝ)/8) ∧ Real.exp ((-1123/65536 : ℝ)/8) ≤ (498930169914325067/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1123/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1673_exp_lower : (920125630554763279/1000000000000000000 : ℝ) ≤ Real.exp ((-83245063311/125000000000 : ℝ)/8) ∧ Real.exp ((-83245063311/125000000000 : ℝ)/8) ≤ (11501570381934541/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83245063311/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1673_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256889900899/125000000000 : ℝ) ≤ 4*Real.exp (561/4096 : ℝ)*Real.exp (-mu (radius 8 (1123/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256889900899/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1123/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1673_exp_radius
  have hrNumeric : (491505179807/500000000000 : ℝ) ≤ Real.exp (-1123/65536 : ℝ) ∧ Real.exp (-1123/65536 : ℝ) ≤ (196602071923/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491505179807/500000000000 : ℝ) ≤ (radius 8 (1123/8192 : ℝ)) ∧ (radius 8 (1123/8192 : ℝ)) ≤ (196602071923/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1123/8192 : ℝ)) (491505179807/500000000000 : ℝ) (196602071923/200000000000 : ℝ) (91775041391/500000000000 : ℝ) (183550082789/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1123/8192 : ℝ)) (491505179807/500000000000 : ℝ) (196602071923/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1123/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491505179807/500000000000 : ℝ) (196602071923/200000000000 : ℝ) (991505179807/1000000000000 : ℝ) (30984536869/31250000000 : ℝ) (495734394513/500000000000 : ℝ) (247867197257/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1123/8192 : ℝ)) 1 (991505179807/1000000000000 : ℝ) (30984536869/31250000000 : ℝ) (495734394513/500000000000 : ℝ) (247867197257/250000000000 : ℝ) (30983968263/31250000000 : ℝ) (495743492209/500000000000 : ℝ) (991486984249/1000000000000 : ℝ) (247871746063/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1123/8192 : ℝ)) 2 (30983968263/31250000000 : ℝ) (495743492209/500000000000 : ℝ) (991486984249/1000000000000 : ℝ) (247871746063/250000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1123/8192 : ℝ)) 3 (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1123/8192 : ℝ)) 4 (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1123/8192 : ℝ)) 5 (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1123/8192 : ℝ)) 6 (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1123/8192 : ℝ)) 7 (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1123/8192 : ℝ))) (91775041391/500000000000 : ℝ) (183550082789/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1123/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (91775041391/500000000000 : ℝ) (183550082789/1000000000000 : ℝ) (591775041391/1000000000000 : ℝ) (118355008279/200000000000 : ℝ) (428427453347/1000000000000 : ℝ) (107106863339/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1123/8192 : ℝ))) 1 (591775041391/1000000000000 : ℝ) (118355008279/200000000000 : ℝ) (428427453347/1000000000000 : ℝ) (107106863339/250000000000 : ℝ) (510101247369/1000000000000 : ℝ) (31881327961/62500000000 : ℝ) (100704056311/200000000000 : ℝ) (503520281563/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1123/8192 : ℝ))) 2 (510101247369/1000000000000 : ℝ) (31881327961/62500000000 : ℝ) (100704056311/200000000000 : ℝ) (503520281563/1000000000000 : ℝ) (253405382231/500000000000 : ℝ) (50681076447/100000000000 : ℝ) (506800082573/1000000000000 : ℝ) (253400041291/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1123/8192 : ℝ))) 3 (253405382231/500000000000 : ℝ) (50681076447/100000000000 : ℝ) (506800082573/1000000000000 : ℝ) (253400041291/500000000000 : ℝ) (506805423517/1000000000000 : ℝ) (253402711763/500000000000 : ℝ) (506805423489/1000000000000 : ℝ) (253402711749/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1123/8192 : ℝ))) 4 (506805423517/1000000000000 : ℝ) (253402711763/500000000000 : ℝ) (506805423489/1000000000000 : ℝ) (253402711749/500000000000 : ℝ) (506805423503/1000000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1123/8192 : ℝ))) 5 (506805423503/1000000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1123/8192 : ℝ))) 6 (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1123/8192 : ℝ))) 7 (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1123/8192 : ℝ)) hmem 8 (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1123/8192 : ℝ))) hcmem 8 (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1123/8192 : ℝ)) (247871746083/250000000000 : ℝ) (198297396867/200000000000 : ℝ) (253402711751/500000000000 : ℝ) (63350677939/125000000000 : ℝ) (802923397093/1000000000000 : ℝ) (802923397113/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1673_exp_lower
  have heNumeric : (256889900899/125000000000 : ℝ)/4 ≤ Real.exp (-83245063311/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256889900899/125000000000 : ℝ)/4 ≤ Real.exp ((561/4096 : ℝ)-(802923397113/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (561/4096 : ℝ) (1123/8192 : ℝ) (802923397113/1000000000000 : ℝ) (256889900899/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1674; no trusted numerical premise.
theorem cover8_leaf1674_exp_radius : (997858436562910319/1000000000000000000 : ℝ) ≤ Real.exp ((-281/16384 : ℝ)/8) ∧ Real.exp ((-281/16384 : ℝ)/8) ≤ (12473230457036379/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-281/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1674_exp_lower : (920126294745561627/1000000000000000000 : ℝ) ≤ Real.exp ((-1331909463413/2000000000000 : ℝ)/8) ∧ Real.exp ((-1331909463413/2000000000000 : ℝ)/8) ≤ (230031573686390407/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1331909463413/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1674_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055131075091/1000000000000 : ℝ) ≤ 4*Real.exp (1123/8192 : ℝ)*Real.exp (-mu (radius 8 (281/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055131075091/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (281/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1674_exp_radius
  have hrNumeric : (49149768009/50000000000 : ℝ) ≤ Real.exp (-281/16384 : ℝ) ∧ Real.exp (-281/16384 : ℝ) ≤ (982995360181/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49149768009/50000000000 : ℝ) ≤ (radius 8 (281/2048 : ℝ)) ∧ (radius 8 (281/2048 : ℝ)) ≤ (982995360181/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (281/2048 : ℝ)) (49149768009/50000000000 : ℝ) (982995360181/1000000000000 : ℝ) (183630394713/1000000000000 : ℝ) (183630394719/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (281/2048 : ℝ)) (49149768009/50000000000 : ℝ) (982995360181/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (281/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49149768009/50000000000 : ℝ) (982995360181/1000000000000 : ℝ) (99149768009/100000000000 : ℝ) (991497680091/1000000000000 : ℝ) (247865306187/250000000000 : ℝ) (3965844899/4000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (281/2048 : ℝ)) 1 (99149768009/100000000000 : ℝ) (991497680091/1000000000000 : ℝ) (247865306187/250000000000 : ℝ) (3965844899/4000000000 : ℝ) (991479452419/1000000000000 : ℝ) (991479452421/1000000000000 : ℝ) (991479452251/1000000000000 : ℝ) (991479452253/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (281/2048 : ℝ)) 2 (991479452419/1000000000000 : ℝ) (991479452421/1000000000000 : ℝ) (991479452251/1000000000000 : ℝ) (991479452253/1000000000000 : ℝ) (198295890467/200000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (281/2048 : ℝ)) 3 (198295890467/200000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (281/2048 : ℝ)) 4 (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (281/2048 : ℝ)) 5 (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (281/2048 : ℝ)) 6 (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (281/2048 : ℝ)) 7 (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (281/2048 : ℝ))) (183630394713/1000000000000 : ℝ) (183630394719/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (281/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (183630394713/1000000000000 : ℝ) (183630394719/1000000000000 : ℝ) (147953799339/250000000000 : ℝ) (7397689967/12500000000 : ℝ) (428521171837/1000000000000 : ℝ) (85704234369/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (281/2048 : ℝ))) 1 (147953799339/250000000000 : ℝ) (7397689967/12500000000 : ℝ) (428521171837/1000000000000 : ℝ) (85704234369/200000000000 : ℝ) (127542046149/250000000000 : ℝ) (510168184603/1000000000000 : ℝ) (503592436283/1000000000000 : ℝ) (50359243629/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (281/2048 : ℝ))) 2 (127542046149/250000000000 : ℝ) (510168184603/1000000000000 : ℝ) (503592436283/1000000000000 : ℝ) (50359243629/100000000000 : ℝ) (506880310439/1000000000000 : ℝ) (506880310447/1000000000000 : ℝ) (101373929389/200000000000 : ℝ) (506869646953/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (281/2048 : ℝ))) 3 (506880310439/1000000000000 : ℝ) (506880310447/1000000000000 : ℝ) (101373929389/200000000000 : ℝ) (506869646953/1000000000000 : ℝ) (126718744673/250000000000 : ℝ) (5068749787/10000000000 : ℝ) (506874978663/1000000000000 : ℝ) (31679686167/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (281/2048 : ℝ))) 4 (126718744673/250000000000 : ℝ) (5068749787/10000000000 : ℝ) (506874978663/1000000000000 : ℝ) (31679686167/62500000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (281/2048 : ℝ))) 5 (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (281/2048 : ℝ))) 6 (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (281/2048 : ℝ))) 7 (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (281/2048 : ℝ)) hmem 8 (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (281/2048 : ℝ))) hcmem 8 (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (281/2048 : ℝ)) (495739726167/500000000000 : ℝ) (991479452337/1000000000000 : ℝ) (506874978677/1000000000000 : ℝ) (253437489343/500000000000 : ℝ) (401519846313/500000000000 : ℝ) (200759923161/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1674_exp_lower
  have heNumeric : (2055131075091/1000000000000 : ℝ)/4 ≤ Real.exp (-1331909463413/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055131075091/1000000000000 : ℝ)/4 ≤ Real.exp ((1123/8192 : ℝ)-(200759923161/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1123/8192 : ℝ) (281/2048 : ℝ) (200759923161/250000000000 : ℝ) (2055131075091/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1650_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1650_certificate
#check SmaleRate.Proofs.cover8_leaf1651_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1651_certificate
#check SmaleRate.Proofs.cover8_leaf1652_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1652_certificate
#check SmaleRate.Proofs.cover8_leaf1653_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1653_certificate
#check SmaleRate.Proofs.cover8_leaf1654_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1654_certificate
#check SmaleRate.Proofs.cover8_leaf1655_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1655_certificate
#check SmaleRate.Proofs.cover8_leaf1656_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1656_certificate
#check SmaleRate.Proofs.cover8_leaf1657_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1657_certificate
#check SmaleRate.Proofs.cover8_leaf1658_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1658_certificate
#check SmaleRate.Proofs.cover8_leaf1659_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1659_certificate
#check SmaleRate.Proofs.cover8_leaf1660_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1660_certificate
#check SmaleRate.Proofs.cover8_leaf1661_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1661_certificate
#check SmaleRate.Proofs.cover8_leaf1662_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1662_certificate
#check SmaleRate.Proofs.cover8_leaf1663_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1663_certificate
#check SmaleRate.Proofs.cover8_leaf1664_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1664_certificate
#check SmaleRate.Proofs.cover8_leaf1665_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1665_certificate
#check SmaleRate.Proofs.cover8_leaf1666_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1666_certificate
#check SmaleRate.Proofs.cover8_leaf1667_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1667_certificate
#check SmaleRate.Proofs.cover8_leaf1668_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1668_certificate
#check SmaleRate.Proofs.cover8_leaf1669_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1669_certificate
#check SmaleRate.Proofs.cover8_leaf1670_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1670_certificate
#check SmaleRate.Proofs.cover8_leaf1671_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1671_certificate
#check SmaleRate.Proofs.cover8_leaf1672_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1672_certificate
#check SmaleRate.Proofs.cover8_leaf1673_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1673_certificate
#check SmaleRate.Proofs.cover8_leaf1674_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1674_certificate
