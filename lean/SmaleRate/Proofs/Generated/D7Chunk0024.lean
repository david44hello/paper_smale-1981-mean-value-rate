/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0600; no trusted numerical premise.
theorem cover7_leaf0600_exp_radius : (498661201975611421/500000000000000000 : ℝ) ≤ Real.exp ((-615/28672 : ℝ)/8) ∧ Real.exp ((-615/28672 : ℝ)/8) ≤ (997322403951222843/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-615/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0600_exp_lower : (114764285601618211/125000000000000000 : ℝ) ≤ Real.exp ((-1708668057/2500000000 : ℝ)/8) ∧ Real.exp ((-1708668057/2500000000 : ℝ)/8) ≤ (918114284812945689/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1708668057/2500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0600_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019453920177/1000000000000 : ℝ) ≤ 4*Real.exp (307/2048 : ℝ)*Real.exp (-mu (radius 7 (615/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019453920177/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (615/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0600_exp_radius
  have hrNumeric : (48938945337/50000000000 : ℝ) ≤ Real.exp (-615/28672 : ℝ) ∧ Real.exp (-615/28672 : ℝ) ≤ (978778906741/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (48938945337/50000000000 : ℝ) ≤ (radius 7 (615/4096 : ℝ)) ∧ (radius 7 (615/4096 : ℝ)) ≤ (978778906741/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (615/4096 : ℝ)) (48938945337/50000000000 : ℝ) (978778906741/1000000000000 : ℝ) (25614891823/125000000000 : ℝ) (20491913459/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (615/4096 : ℝ)) (48938945337/50000000000 : ℝ) (978778906741/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (615/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (48938945337/50000000000 : ℝ) (978778906741/1000000000000 : ℝ) (98938945337/100000000000 : ℝ) (989389453371/1000000000000 : ℝ) (989332556191/1000000000000 : ℝ) (30916642381/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (615/4096 : ℝ)) 1 (98938945337/100000000000 : ℝ) (989389453371/1000000000000 : ℝ) (989332556191/1000000000000 : ℝ) (30916642381/31250000000 : ℝ) (49468050239/50000000000 : ℝ) (494680502391/500000000000 : ℝ) (989361004371/1000000000000 : ℝ) (989361004373/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (615/4096 : ℝ)) 2 (49468050239/50000000000 : ℝ) (494680502391/500000000000 : ℝ) (989361004371/1000000000000 : ℝ) (989361004373/1000000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (615/4096 : ℝ)) 3 (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (615/4096 : ℝ)) 4 (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (615/4096 : ℝ)) 5 (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (615/4096 : ℝ)) 6 (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (615/4096 : ℝ)) 7 (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (615/4096 : ℝ))) (25614891823/125000000000 : ℝ) (20491913459/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (615/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (25614891823/125000000000 : ℝ) (20491913459/100000000000 : ℝ) (150614891823/250000000000 : ℝ) (120491913459/200000000000 : ℝ) (90535989437/200000000000 : ℝ) (452679947193/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (615/4096 : ℝ))) 1 (150614891823/250000000000 : ℝ) (120491913459/200000000000 : ℝ) (90535989437/200000000000 : ℝ) (452679947193/1000000000000 : ℝ) (263784878619/500000000000 : ℝ) (131892439311/250000000000 : ℝ) (130556827929/250000000000 : ℝ) (522227311723/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (615/4096 : ℝ))) 2 (263784878619/500000000000 : ℝ) (131892439311/250000000000 : ℝ) (130556827929/250000000000 : ℝ) (522227311723/1000000000000 : ℝ) (524898534477/1000000000000 : ℝ) (131224633621/250000000000 : ℝ) (52489173747/100000000000 : ℝ) (262445868739/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (615/4096 : ℝ))) 3 (524898534477/1000000000000 : ℝ) (131224633621/250000000000 : ℝ) (52489173747/100000000000 : ℝ) (262445868739/500000000000 : ℝ) (524895135973/1000000000000 : ℝ) (524895135981/1000000000000 : ℝ) (262447567981/500000000000 : ℝ) (52489513597/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (615/4096 : ℝ))) 4 (524895135973/1000000000000 : ℝ) (524895135981/1000000000000 : ℝ) (262447567981/500000000000 : ℝ) (52489513597/100000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (615/4096 : ℝ))) 5 (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (615/4096 : ℝ))) 6 (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (615/4096 : ℝ))) 7 (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (615/4096 : ℝ)) hmem 8 (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (615/4096 : ℝ))) hcmem 8 (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (615/4096 : ℝ)) (39574440183/40000000000 : ℝ) (494680502289/500000000000 : ℝ) (524895135967/1000000000000 : ℝ) (65611891997/125000000000 : ℝ) (208342391633/250000000000 : ℝ) (16667391331/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0600_exp_lower
  have heNumeric : (2019453920177/1000000000000 : ℝ)/4 ≤ Real.exp (-1708668057/2500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019453920177/1000000000000 : ℝ)/4 ≤ Real.exp ((307/2048 : ℝ)-(16667391331/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (307/2048 : ℝ) (615/4096 : ℝ) (16667391331/20000000000 : ℝ) (2019453920177/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0601; no trusted numerical premise.
theorem cover7_leaf0601_exp_radius : (997318055980075189/1000000000000000000 : ℝ) ≤ Real.exp ((-11/512 : ℝ)/8) ∧ Real.exp ((-11/512 : ℝ)/8) ≤ (99731805598007519/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-11/512 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0601_exp_lower : (229529013875793881/250000000000000000 : ℝ) ≤ Real.exp ((-170862948471/250000000000 : ℝ)/8) ∧ Real.exp ((-170862948471/250000000000 : ℝ)/8) ≤ (36724642220127021/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170862948471/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0601_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009742539201/500000000000 : ℝ) ≤ 4*Real.exp (615/4096 : ℝ)*Real.exp (-mu (radius 7 (77/512 : ℝ))) ∧ (2019/1000 : ℝ) < (1009742539201/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (77/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0601_exp_radius
  have hrNumeric : (244686192559/250000000000 : ℝ) ≤ Real.exp (-11/512 : ℝ) ∧ Real.exp (-11/512 : ℝ) ≤ (978744770237/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (244686192559/250000000000 : ℝ) ≤ (radius 7 (77/512 : ℝ)) ∧ (radius 7 (77/512 : ℝ)) ≤ (978744770237/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (77/512 : ℝ)) (244686192559/250000000000 : ℝ) (978744770237/1000000000000 : ℝ) (4101642341/20000000000 : ℝ) (41016423411/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (77/512 : ℝ)) (244686192559/250000000000 : ℝ) (978744770237/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (77/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (244686192559/250000000000 : ℝ) (978744770237/1000000000000 : ℝ) (494686192559/500000000000 : ℝ) (989372385119/1000000000000 : ℝ) (989315303751/1000000000000 : ℝ) (123664412969/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (77/512 : ℝ)) 1 (494686192559/500000000000 : ℝ) (989372385119/1000000000000 : ℝ) (989315303751/1000000000000 : ℝ) (123664412969/125000000000 : ℝ) (494671922217/500000000000 : ℝ) (247335961109/250000000000 : ℝ) (494671922011/500000000000 : ℝ) (123667980503/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (77/512 : ℝ)) 2 (494671922217/500000000000 : ℝ) (247335961109/250000000000 : ℝ) (494671922011/500000000000 : ℝ) (123667980503/125000000000 : ℝ) (247335961057/250000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (77/512 : ℝ)) 3 (247335961057/250000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (77/512 : ℝ)) 4 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (77/512 : ℝ)) 5 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (77/512 : ℝ)) 6 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (77/512 : ℝ)) 7 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (77/512 : ℝ))) (4101642341/20000000000 : ℝ) (41016423411/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (77/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4101642341/20000000000 : ℝ) (41016423411/200000000000 : ℝ) (24101642341/40000000000 : ℝ) (18829408079/31250000000 : ℝ) (226429965469/500000000000 : ℝ) (90571986189/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (77/512 : ℝ))) 1 (24101642341/40000000000 : ℝ) (18829408079/31250000000 : ℝ) (226429965469/500000000000 : ℝ) (90571986189/200000000000 : ℝ) (527700494731/1000000000000 : ℝ) (527700494737/1000000000000 : ℝ) (522366444319/1000000000000 : ℝ) (20894657773/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (77/512 : ℝ))) 2 (527700494731/1000000000000 : ℝ) (527700494737/1000000000000 : ℝ) (522366444319/1000000000000 : ℝ) (20894657773/40000000000 : ℝ) (21001338781/40000000000 : ℝ) (525033469531/1000000000000 : ℝ) (105005339121/200000000000 : ℝ) (131256673903/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (77/512 : ℝ))) 3 (21001338781/40000000000 : ℝ) (525033469531/1000000000000 : ℝ) (105005339121/200000000000 : ℝ) (131256673903/250000000000 : ℝ) (105006016513/200000000000 : ℝ) (131257520643/250000000000 : ℝ) (262515041277/500000000000 : ℝ) (525030082561/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (77/512 : ℝ))) 4 (105006016513/200000000000 : ℝ) (131257520643/250000000000 : ℝ) (262515041277/500000000000 : ℝ) (525030082561/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (77/512 : ℝ))) 5 (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (77/512 : ℝ))) 6 (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (77/512 : ℝ))) 7 (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (77/512 : ℝ)) hmem 8 (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (77/512 : ℝ))) hcmem 8 (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (77/512 : ℝ)) (989343844227/1000000000000 : ℝ) (98934384423/100000000000 : ℝ) (525030082559/1000000000000 : ℝ) (525030082567/1000000000000 : ℝ) (833598278243/1000000000000 : ℝ) (833598278259/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0601_exp_lower
  have heNumeric : (1009742539201/500000000000 : ℝ)/4 ≤ Real.exp (-170862948471/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009742539201/500000000000 : ℝ)/4 ≤ Real.exp ((615/4096 : ℝ)-(833598278259/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (615/4096 : ℝ) (77/512 : ℝ) (833598278259/1000000000000 : ℝ) (1009742539201/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0602; no trusted numerical premise.
theorem cover7_leaf0602_exp_radius : (498654680047323313/500000000000000000 : ℝ) ≤ Real.exp ((-309/14336 : ℝ)/8) ∧ Real.exp ((-309/14336 : ℝ)/8) ≤ (997309360094646627/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-309/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0602_exp_lower : (57380728941107809/62500000000000000 : ℝ) ≤ Real.exp ((-85458042521/125000000000 : ℝ)/8) ∧ Real.exp ((-85458042521/125000000000 : ℝ)/8) ≤ (183618332611544989/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85458042521/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0602_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009527944983/500000000000 : ℝ) ≤ 4*Real.exp (77/512 : ℝ)*Real.exp (-mu (radius 7 (309/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009527944983/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (309/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0602_exp_radius
  have hrNumeric : (611672813/625000000 : ℝ) ≤ Real.exp (-309/14336 : ℝ) ∧ Real.exp (-309/14336 : ℝ) ≤ (978676500801/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (611672813/625000000 : ℝ) ≤ (radius 7 (309/2048 : ℝ)) ∧ (radius 7 (309/2048 : ℝ)) ≤ (978676500801/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (309/2048 : ℝ)) (611672813/625000000 : ℝ) (978676500801/1000000000000 : ℝ) (205407659983/1000000000000 : ℝ) (205407659989/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (309/2048 : ℝ)) (611672813/625000000 : ℝ) (978676500801/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (309/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (611672813/625000000 : ℝ) (978676500801/1000000000000 : ℝ) (1236672813/1250000000 : ℝ) (989338250401/1000000000000 : ℝ) (989280799773/1000000000000 : ℝ) (494640399887/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (309/2048 : ℝ)) 1 (1236672813/1250000000 : ℝ) (989338250401/1000000000000 : ℝ) (989280799773/1000000000000 : ℝ) (494640399887/500000000000 : ℝ) (494654762543/500000000000 : ℝ) (30915922659/31250000000 : ℝ) (989309524669/1000000000000 : ℝ) (989309524671/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (309/2048 : ℝ)) 2 (494654762543/500000000000 : ℝ) (30915922659/31250000000 : ℝ) (989309524669/1000000000000 : ℝ) (989309524671/1000000000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (309/2048 : ℝ)) 3 (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (309/2048 : ℝ)) 4 (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (309/2048 : ℝ)) 5 (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (309/2048 : ℝ)) 6 (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (309/2048 : ℝ)) 7 (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (309/2048 : ℝ))) (205407659983/1000000000000 : ℝ) (205407659989/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (309/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (205407659983/1000000000000 : ℝ) (205407659989/1000000000000 : ℝ) (602703829991/1000000000000 : ℝ) (120540765999/200000000000 : ℝ) (453219218461/1000000000000 : ℝ) (453219218469/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (309/2048 : ℝ))) 1 (602703829991/1000000000000 : ℝ) (120540765999/200000000000 : ℝ) (453219218461/1000000000000 : ℝ) (453219218469/1000000000000 : ℝ) (263980762113/500000000000 : ℝ) (65995190529/125000000000 : ℝ) (522644199041/1000000000000 : ℝ) (522644199049/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (309/2048 : ℝ))) 2 (263980762113/500000000000 : ℝ) (65995190529/125000000000 : ℝ) (522644199041/1000000000000 : ℝ) (522644199049/1000000000000 : ℝ) (525302861633/1000000000000 : ℝ) (525302861641/1000000000000 : ℝ) (525296133579/1000000000000 : ℝ) (525296133587/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (309/2048 : ℝ))) 3 (525302861633/1000000000000 : ℝ) (525302861641/1000000000000 : ℝ) (525296133579/1000000000000 : ℝ) (525296133587/1000000000000 : ℝ) (262649748803/500000000000 : ℝ) (262649748807/500000000000 : ℝ) (105059899519/200000000000 : ℝ) (131324874401/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (309/2048 : ℝ))) 4 (262649748803/500000000000 : ℝ) (262649748807/500000000000 : ℝ) (105059899519/200000000000 : ℝ) (131324874401/250000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (309/2048 : ℝ))) 5 (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (309/2048 : ℝ))) 6 (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (309/2048 : ℝ))) 7 (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (309/2048 : ℝ)) hmem 8 (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (309/2048 : ℝ))) hcmem 8 (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (309/2048 : ℝ)) (989309524877/1000000000000 : ℝ) (12366369061/12500000000 : ℝ) (164156093/312500000 : ℝ) (525299497609/1000000000000 : ℝ) (16681099303/20000000000 : ℝ) (52128435323/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0602_exp_lower
  have heNumeric : (1009527944983/500000000000 : ℝ)/4 ≤ Real.exp (-85458042521/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009527944983/500000000000 : ℝ)/4 ≤ Real.exp ((77/512 : ℝ)-(52128435323/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (77/512 : ℝ) (309/2048 : ℝ) (52128435323/62500000000 : ℝ) (1009527944983/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0603; no trusted numerical premise.
theorem cover7_leaf0603_exp_radius : (249325166071259959/250000000000000000 : ℝ) ≤ Real.exp ((-155/7168 : ℝ)/8) ∧ Real.exp ((-155/7168 : ℝ)/8) ≤ (997300664285039837/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-155/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0603_exp_lower : (918095401043522171/1000000000000000000 : ℝ) ≤ Real.exp ((-683631768447/1000000000000 : ℝ)/8) ∧ Real.exp ((-683631768447/1000000000000 : ℝ)/8) ≤ (229523850260880543/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683631768447/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0603_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009560827581/500000000000 : ℝ) ≤ 4*Real.exp (309/2048 : ℝ)*Real.exp (-mu (radius 7 (155/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (1009560827581/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (155/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0603_exp_radius
  have hrNumeric : (489304118063/500000000000 : ℝ) ≤ Real.exp (-155/7168 : ℝ) ∧ Real.exp (-155/7168 : ℝ) ≤ (978608236127/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489304118063/500000000000 : ℝ) ≤ (radius 7 (155/1024 : ℝ)) ∧ (radius 7 (155/1024 : ℝ)) ≤ (978608236127/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (155/1024 : ℝ)) (489304118063/500000000000 : ℝ) (978608236127/1000000000000 : ℝ) (102866321243/500000000000 : ℝ) (51433160623/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (155/1024 : ℝ)) (489304118063/500000000000 : ℝ) (978608236127/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (155/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489304118063/500000000000 : ℝ) (978608236127/1000000000000 : ℝ) (989304118063/1000000000000 : ℝ) (61831507379/62500000000 : ℝ) (494623148499/500000000000 : ℝ) (989246297/1000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (155/1024 : ℝ)) 1 (989304118063/1000000000000 : ℝ) (61831507379/62500000000 : ℝ) (494623148499/500000000000 : ℝ) (989246297/1000000000 : ℝ) (98927520753/100000000000 : ℝ) (247318801883/250000000000 : ℝ) (247318801777/250000000000 : ℝ) (98927520711/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (155/1024 : ℝ)) 2 (98927520753/100000000000 : ℝ) (247318801883/250000000000 : ℝ) (247318801777/250000000000 : ℝ) (98927520711/100000000000 : ℝ) (989275207319/1000000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (155/1024 : ℝ)) 3 (989275207319/1000000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (155/1024 : ℝ)) 4 (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (155/1024 : ℝ)) 5 (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (155/1024 : ℝ)) 6 (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (155/1024 : ℝ)) 7 (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (155/1024 : ℝ))) (102866321243/500000000000 : ℝ) (51433160623/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (155/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (102866321243/500000000000 : ℝ) (51433160623/250000000000 : ℝ) (602866321243/1000000000000 : ℝ) (301433160623/500000000000 : ℝ) (226788801799/500000000000 : ℝ) (90715520721/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (155/1024 : ℝ))) 1 (602866321243/1000000000000 : ℝ) (301433160623/500000000000 : ℝ) (226788801799/500000000000 : ℝ) (90715520721/200000000000 : ℝ) (26411098121/50000000000 : ℝ) (264110981213/500000000000 : ℝ) (32682579773/62500000000 : ℝ) (4183370211/8000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (155/1024 : ℝ))) 2 (26411098121/50000000000 : ℝ) (264110981213/500000000000 : ℝ) (32682579773/62500000000 : ℝ) (4183370211/8000000000 : ℝ) (262785809697/500000000000 : ℝ) (525571619401/1000000000000 : ℝ) (656956171/1250000000 : ℝ) (65695617101/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (155/1024 : ℝ))) 3 (262785809697/500000000000 : ℝ) (525571619401/1000000000000 : ℝ) (656956171/1250000000 : ℝ) (65695617101/125000000000 : ℝ) (525568278097/1000000000000 : ℝ) (105113655621/200000000000 : ℝ) (262784139043/500000000000 : ℝ) (262784139047/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (155/1024 : ℝ))) 4 (525568278097/1000000000000 : ℝ) (105113655621/200000000000 : ℝ) (262784139043/500000000000 : ℝ) (262784139047/500000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (155/1024 : ℝ))) 5 (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (155/1024 : ℝ))) 6 (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (155/1024 : ℝ))) 7 (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (155/1024 : ℝ)) hmem 8 (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (155/1024 : ℝ))) hcmem 8 (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (155/1024 : ℝ)) (494637603659/500000000000 : ℝ) (989275207321/1000000000000 : ℝ) (525568278091/1000000000000 : ℝ) (5255682781/10000000000 : ℝ) (834510674679/1000000000000 : ℝ) (834510674697/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0603_exp_lower
  have heNumeric : (1009560827581/500000000000 : ℝ)/4 ≤ Real.exp (-683631768447/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009560827581/500000000000 : ℝ)/4 ≤ Real.exp ((309/2048 : ℝ)-(834510674697/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (309/2048 : ℝ) (155/1024 : ℝ) (834510674697/1000000000000 : ℝ) (1009560827581/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0604; no trusted numerical premise.
theorem cover7_leaf0604_exp_radius : (498645984275627079/500000000000000000 : ℝ) ≤ Real.exp ((-311/14336 : ℝ)/8) ∧ Real.exp ((-311/14336 : ℝ)/8) ≤ (997291968551254159/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-311/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0604_exp_lower : (183619850116009743/200000000000000000 : ℝ) ≤ Real.exp ((-170899556211/250000000000 : ℝ)/8) ∧ Real.exp ((-170899556211/250000000000 : ℝ)/8) ≤ (229524812645012179/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170899556211/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0604_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009594692457/500000000000 : ℝ) ≤ 4*Real.exp (155/1024 : ℝ)*Real.exp (-mu (radius 7 (311/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009594692457/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (311/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0604_exp_radius
  have hrNumeric : (489269988107/500000000000 : ℝ) ≤ Real.exp (-311/14336 : ℝ) ∧ Real.exp (-311/14336 : ℝ) ≤ (195707995243/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489269988107/500000000000 : ℝ) ≤ (radius 7 (311/2048 : ℝ)) ∧ (radius 7 (311/2048 : ℝ)) ≤ (195707995243/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (311/2048 : ℝ)) (489269988107/500000000000 : ℝ) (195707995243/200000000000 : ℝ) (103028533607/500000000000 : ℝ) (10302853361/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (311/2048 : ℝ)) (489269988107/500000000000 : ℝ) (195707995243/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (311/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489269988107/500000000000 : ℝ) (195707995243/200000000000 : ℝ) (989269988107/1000000000000 : ℝ) (247317497027/250000000000 : ℝ) (247302948857/250000000000 : ℝ) (989211795429/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (311/2048 : ℝ)) 1 (989269988107/1000000000000 : ℝ) (247317497027/250000000000 : ℝ) (247302948857/250000000000 : ℝ) (989211795429/1000000000000 : ℝ) (989240891767/1000000000000 : ℝ) (989240891769/1000000000000 : ℝ) (989240891339/1000000000000 : ℝ) (989240891341/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (311/2048 : ℝ)) 2 (989240891767/1000000000000 : ℝ) (989240891769/1000000000000 : ℝ) (989240891339/1000000000000 : ℝ) (989240891341/1000000000000 : ℝ) (989240891553/1000000000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (311/2048 : ℝ)) 3 (989240891553/1000000000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (311/2048 : ℝ)) 4 (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (311/2048 : ℝ)) 5 (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (311/2048 : ℝ)) 6 (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (311/2048 : ℝ)) 7 (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (311/2048 : ℝ))) (103028533607/500000000000 : ℝ) (10302853361/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (311/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (103028533607/500000000000 : ℝ) (10302853361/50000000000 : ℝ) (603028533607/1000000000000 : ℝ) (60302853361/100000000000 : ℝ) (45393509141/100000000000 : ℝ) (226967545709/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (311/2048 : ℝ))) 1 (603028533607/1000000000000 : ℝ) (60302853361/100000000000 : ℝ) (45393509141/100000000000 : ℝ) (226967545709/500000000000 : ℝ) (132120453127/250000000000 : ℝ) (264240906257/500000000000 : ℝ) (3269985501/6250000000 : ℝ) (523197680167/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (311/2048 : ℝ))) 2 (132120453127/250000000000 : ℝ) (264240906257/500000000000 : ℝ) (3269985501/6250000000 : ℝ) (523197680167/1000000000000 : ℝ) (262919873167/500000000000 : ℝ) (525839746341/1000000000000 : ℝ) (328645693/625000000 : ℝ) (65729138601/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (311/2048 : ℝ))) 3 (262919873167/500000000000 : ℝ) (525839746341/1000000000000 : ℝ) (328645693/625000000 : ℝ) (65729138601/125000000000 : ℝ) (525836427567/1000000000000 : ℝ) (21033457103/40000000000 : ℝ) (131459106889/250000000000 : ℝ) (105167285513/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (311/2048 : ℝ))) 4 (525836427567/1000000000000 : ℝ) (21033457103/40000000000 : ℝ) (131459106889/250000000000 : ℝ) (105167285513/200000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (311/2048 : ℝ))) 5 (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (311/2048 : ℝ))) 6 (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (311/2048 : ℝ))) 7 (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (311/2048 : ℝ)) hmem 8 (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (311/2048 : ℝ))) hcmem 8 (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (311/2048 : ℝ)) (30913777861/31250000000 : ℝ) (197848178311/200000000000 : ℝ) (525836427561/1000000000000 : ℝ) (52583642757/100000000000 : ℝ) (417482706163/500000000000 : ℝ) (104370676543/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0604_exp_lower
  have heNumeric : (1009594692457/500000000000 : ℝ)/4 ≤ Real.exp (-170899556211/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009594692457/500000000000 : ℝ)/4 ≤ Real.exp ((155/1024 : ℝ)-(104370676543/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (155/1024 : ℝ) (311/2048 : ℝ) (104370676543/125000000000 : ℝ) (1009594692457/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0605; no trusted numerical premise.
theorem cover7_leaf0605_exp_radius : (997283272893288931/1000000000000000000 : ℝ) ≤ Real.exp ((-39/1792 : ℝ)/8) ∧ Real.exp ((-39/1792 : ℝ)/8) ≤ (249320818223322233/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-39/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0605_exp_lower : (459051605520419897/500000000000000000 : ℝ) ≤ Real.exp ((-68356371483/100000000000 : ℝ)/8) ∧ Real.exp ((-68356371483/100000000000 : ℝ)/8) ≤ (183620642208167959/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-68356371483/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0605_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201925906837/100000000000 : ℝ) ≤ 4*Real.exp (311/2048 : ℝ)*Real.exp (-mu (radius 7 (39/256 : ℝ))) ∧ (2019/1000 : ℝ) < (201925906837/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (39/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0605_exp_radius
  have hrNumeric : (489235860531/500000000000 : ℝ) ≤ Real.exp (-39/1792 : ℝ) ∧ Real.exp (-39/1792 : ℝ) ≤ (978471721063/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489235860531/500000000000 : ℝ) ≤ (radius 7 (39/256 : ℝ)) ∧ (radius 7 (39/256 : ℝ)) ≤ (978471721063/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (39/256 : ℝ)) (489235860531/500000000000 : ℝ) (978471721063/1000000000000 : ℝ) (206380936813/1000000000000 : ℝ) (206380936819/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (39/256 : ℝ)) (489235860531/500000000000 : ℝ) (978471721063/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (39/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489235860531/500000000000 : ℝ) (978471721063/1000000000000 : ℝ) (989235860531/1000000000000 : ℝ) (247308965133/250000000000 : ℝ) (989177295059/1000000000000 : ℝ) (989177295061/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (39/256 : ℝ)) 1 (989235860531/1000000000000 : ℝ) (247308965133/250000000000 : ℝ) (989177295059/1000000000000 : ℝ) (989177295061/1000000000000 : ℝ) (197841315559/200000000000 : ℝ) (989206577797/1000000000000 : ℝ) (989206577361/1000000000000 : ℝ) (247301644341/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (39/256 : ℝ)) 2 (197841315559/200000000000 : ℝ) (989206577797/1000000000000 : ℝ) (989206577361/1000000000000 : ℝ) (247301644341/250000000000 : ℝ) (494603288789/500000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (39/256 : ℝ)) 3 (494603288789/500000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (39/256 : ℝ)) 4 (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (39/256 : ℝ)) 5 (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (39/256 : ℝ)) 6 (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (39/256 : ℝ)) 7 (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (39/256 : ℝ))) (206380936813/1000000000000 : ℝ) (206380936819/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (39/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (206380936813/1000000000000 : ℝ) (206380936819/1000000000000 : ℝ) (301595234203/500000000000 : ℝ) (60319046841/100000000000 : ℝ) (454291686929/1000000000000 : ℝ) (56786460867/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (39/256 : ℝ))) 1 (301595234203/500000000000 : ℝ) (60319046841/100000000000 : ℝ) (454291686929/1000000000000 : ℝ) (56786460867/125000000000 : ℝ) (528741077667/1000000000000 : ℝ) (528741077673/1000000000000 : ℝ) (261736707127/500000000000 : ℝ) (523473414261/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (39/256 : ℝ))) 2 (528741077667/1000000000000 : ℝ) (528741077673/1000000000000 : ℝ) (261736707127/500000000000 : ℝ) (523473414261/1000000000000 : ℝ) (13152681149/25000000000 : ℝ) (526107245967/1000000000000 : ℝ) (52610065309/100000000000 : ℝ) (263050326549/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (39/256 : ℝ))) 3 (13152681149/25000000000 : ℝ) (526107245967/1000000000000 : ℝ) (52610065309/100000000000 : ℝ) (263050326549/500000000000 : ℝ) (21044157981/40000000000 : ℝ) (526103949533/1000000000000 : ℝ) (263051974757/500000000000 : ℝ) (526103949523/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (39/256 : ℝ))) 4 (21044157981/40000000000 : ℝ) (526103949533/1000000000000 : ℝ) (263051974757/500000000000 : ℝ) (526103949523/1000000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (39/256 : ℝ))) 5 (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (39/256 : ℝ))) 6 (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (39/256 : ℝ))) 7 (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (39/256 : ℝ)) hmem 8 (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (39/256 : ℝ))) hcmem 8 (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (39/256 : ℝ)) (989206577577/1000000000000 : ℝ) (989206577581/1000000000000 : ℝ) (526103949519/1000000000000 : ℝ) (65762993691/125000000000 : ℝ) (835419183561/1000000000000 : ℝ) (41770959179/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0605_exp_lower
  have heNumeric : (201925906837/100000000000 : ℝ)/4 ≤ Real.exp (-68356371483/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201925906837/100000000000 : ℝ)/4 ≤ Real.exp ((311/2048 : ℝ)-(41770959179/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (311/2048 : ℝ) (39/256 : ℝ) (41770959179/50000000000 : ℝ) (201925906837/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0606; no trusted numerical premise.
theorem cover7_leaf0606_exp_radius : (498637288655571747/500000000000000000 : ℝ) ≤ Real.exp ((-313/14336 : ℝ)/8) ∧ Real.exp ((-313/14336 : ℝ)/8) ≤ (199454915462228699/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-313/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0606_exp_lower : (918107281808870753/1000000000000000000 : ℝ) ≤ Real.exp ((-341764121897/500000000000 : ℝ)/8) ∧ Real.exp ((-341764121897/500000000000 : ℝ)/8) ≤ (459053640904435377/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341764121897/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0606_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019330694851/1000000000000 : ℝ) ≤ 4*Real.exp (39/256 : ℝ)*Real.exp (-mu (radius 7 (313/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019330694851/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (313/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0606_exp_radius
  have hrNumeric : (61150216917/62500000000 : ℝ) ≤ Real.exp (-313/14336 : ℝ) ∧ Real.exp (-313/14336 : ℝ) ≤ (978403470673/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61150216917/62500000000 : ℝ) ≤ (radius 7 (313/2048 : ℝ)) ∧ (radius 7 (313/2048 : ℝ)) ≤ (978403470673/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (313/2048 : ℝ)) (61150216917/62500000000 : ℝ) (978403470673/1000000000000 : ℝ) (206704253887/1000000000000 : ℝ) (51676063473/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (313/2048 : ℝ)) (61150216917/62500000000 : ℝ) (978403470673/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (313/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61150216917/62500000000 : ℝ) (978403470673/1000000000000 : ℝ) (123650216917/125000000000 : ℝ) (989201735337/1000000000000 : ℝ) (197828559179/200000000000 : ℝ) (989142795897/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (313/2048 : ℝ)) 1 (123650216917/125000000000 : ℝ) (989201735337/1000000000000 : ℝ) (197828559179/200000000000 : ℝ) (989142795897/1000000000000 : ℝ) (197834453123/200000000000 : ℝ) (989172265617/1000000000000 : ℝ) (123646533147/125000000000 : ℝ) (989172265179/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (313/2048 : ℝ)) 2 (197834453123/200000000000 : ℝ) (989172265617/1000000000000 : ℝ) (123646533147/125000000000 : ℝ) (989172265179/1000000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (313/2048 : ℝ)) 3 (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (313/2048 : ℝ)) 4 (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (313/2048 : ℝ)) 5 (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (313/2048 : ℝ)) 6 (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (313/2048 : ℝ)) 7 (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (313/2048 : ℝ))) (206704253887/1000000000000 : ℝ) (51676063473/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (313/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (206704253887/1000000000000 : ℝ) (51676063473/250000000000 : ℝ) (603352126943/1000000000000 : ℝ) (301676063473/500000000000 : ℝ) (454647395117/1000000000000 : ℝ) (454647395123/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (313/2048 : ℝ))) 1 (603352126943/1000000000000 : ℝ) (301676063473/500000000000 : ℝ) (454647395117/1000000000000 : ℝ) (454647395123/1000000000000 : ℝ) (52899976103/100000000000 : ℝ) (105799952207/200000000000 : ℝ) (261874241217/500000000000 : ℝ) (13093712061/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (313/2048 : ℝ))) 2 (52899976103/100000000000 : ℝ) (105799952207/200000000000 : ℝ) (261874241217/500000000000 : ℝ) (13093712061/25000000000 : ℝ) (131593530433/250000000000 : ℝ) (263187060869/500000000000 : ℝ) (263183786567/500000000000 : ℝ) (26318378657/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (313/2048 : ℝ))) 3 (131593530433/250000000000 : ℝ) (263187060869/500000000000 : ℝ) (263183786567/500000000000 : ℝ) (26318378657/50000000000 : ℝ) (526370847433/1000000000000 : ℝ) (526370847439/1000000000000 : ℝ) (263185423711/500000000000 : ℝ) (526370847429/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (313/2048 : ℝ))) 4 (526370847433/1000000000000 : ℝ) (526370847439/1000000000000 : ℝ) (263185423711/500000000000 : ℝ) (526370847429/1000000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (313/2048 : ℝ))) 5 (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (313/2048 : ℝ))) 6 (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (313/2048 : ℝ))) 7 (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (313/2048 : ℝ)) hmem 8 (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (313/2048 : ℝ))) hcmem 8 (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (313/2048 : ℝ)) (197834453079/200000000000 : ℝ) (494586132699/500000000000 : ℝ) (526370847427/1000000000000 : ℝ) (263185423717/500000000000 : ℝ) (41793599689/50000000000 : ℝ) (417935996897/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0606_exp_lower
  have heNumeric : (2019330694851/1000000000000 : ℝ)/4 ≤ Real.exp (-341764121897/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019330694851/1000000000000 : ℝ)/4 ≤ Real.exp ((39/256 : ℝ)-(417935996897/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (39/256 : ℝ) (313/2048 : ℝ) (417935996897/500000000000 : ℝ) (2019330694851/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0607; no trusted numerical premise.
theorem cover7_leaf0607_exp_radius : (199453176360963437/200000000000000000 : ℝ) ≤ Real.exp ((-157/7168 : ℝ)/8) ∧ Real.exp ((-157/7168 : ℝ)/8) ≤ (498632940902408593/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-157/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0607_exp_lower : (459055731134146757/500000000000000000 : ℝ) ≤ Real.exp ((-136698363423/200000000000 : ℝ)/8) ∧ Real.exp ((-136698363423/200000000000 : ℝ)/8) ≤ (183622292453658703/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136698363423/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0607_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009702126851/500000000000 : ℝ) ≤ 4*Real.exp (313/2048 : ℝ)*Real.exp (-mu (radius 7 (157/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (1009702126851/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (157/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0607_exp_radius
  have hrNumeric : (489167612521/500000000000 : ℝ) ≤ Real.exp (-157/7168 : ℝ) ∧ Real.exp (-157/7168 : ℝ) ≤ (978335225043/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (489167612521/500000000000 : ℝ) ≤ (radius 7 (157/1024 : ℝ)) ∧ (radius 7 (157/1024 : ℝ)) ≤ (978335225043/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (157/1024 : ℝ)) (489167612521/500000000000 : ℝ) (978335225043/1000000000000 : ℝ) (103513510519/500000000000 : ℝ) (51756755261/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (157/1024 : ℝ)) (489167612521/500000000000 : ℝ) (978335225043/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (157/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (489167612521/500000000000 : ℝ) (978335225043/1000000000000 : ℝ) (989167612521/1000000000000 : ℝ) (494583806261/500000000000 : ℝ) (494554148967/500000000000 : ℝ) (197821659587/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (157/1024 : ℝ)) 1 (989167612521/1000000000000 : ℝ) (494583806261/500000000000 : ℝ) (494554148967/500000000000 : ℝ) (197821659587/200000000000 : ℝ) (989137955227/1000000000000 : ℝ) (989137955229/1000000000000 : ℝ) (494568977391/500000000000 : ℝ) (30910561087/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (157/1024 : ℝ)) 2 (989137955227/1000000000000 : ℝ) (989137955229/1000000000000 : ℝ) (494568977391/500000000000 : ℝ) (30910561087/31250000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (157/1024 : ℝ)) 3 (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (157/1024 : ℝ)) 4 (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (157/1024 : ℝ)) 5 (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (157/1024 : ℝ)) 6 (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (157/1024 : ℝ)) 7 (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (157/1024 : ℝ))) (103513510519/500000000000 : ℝ) (51756755261/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (157/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (103513510519/500000000000 : ℝ) (51756755261/250000000000 : ℝ) (603513510519/1000000000000 : ℝ) (301756755261/500000000000 : ℝ) (91000444183/200000000000 : ℝ) (455002220923/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (157/1024 : ℝ))) 1 (603513510519/1000000000000 : ℝ) (301756755261/500000000000 : ℝ) (91000444183/200000000000 : ℝ) (455002220923/1000000000000 : ℝ) (529257865717/1000000000000 : ℝ) (529257865723/1000000000000 : ℝ) (131005722117/250000000000 : ℝ) (262011444237/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (157/1024 : ℝ))) 2 (529257865717/1000000000000 : ℝ) (529257865723/1000000000000 : ℝ) (131005722117/250000000000 : ℝ) (262011444237/500000000000 : ℝ) (131660094273/250000000000 : ℝ) (526640377099/1000000000000 : ℝ) (526633872379/1000000000000 : ℝ) (263316936193/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (157/1024 : ℝ))) 3 (131660094273/250000000000 : ℝ) (526640377099/1000000000000 : ℝ) (526633872379/1000000000000 : ℝ) (263316936193/500000000000 : ℝ) (105327424947/200000000000 : ℝ) (526637124743/1000000000000 : ℝ) (21065484989/40000000000 : ℝ) (526637124733/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (157/1024 : ℝ))) 4 (105327424947/200000000000 : ℝ) (526637124743/1000000000000 : ℝ) (21065484989/40000000000 : ℝ) (526637124733/1000000000000 : ℝ) (52663712473/100000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (157/1024 : ℝ))) 5 (52663712473/100000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (157/1024 : ℝ))) 6 (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (157/1024 : ℝ))) 7 (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (157/1024 : ℝ)) hmem 8 (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (157/1024 : ℝ))) hcmem 8 (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (157/1024 : ℝ)) (247284488751/250000000000 : ℝ) (989137955007/1000000000000 : ℝ) (526637124729/1000000000000 : ℝ) (263318562369/500000000000 : ℝ) (836323848347/1000000000000 : ℝ) (167264769673/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0607_exp_lower
  have heNumeric : (1009702126851/500000000000 : ℝ)/4 ≤ Real.exp (-136698363423/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009702126851/500000000000 : ℝ)/4 ≤ Real.exp ((313/2048 : ℝ)-(167264769673/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (313/2048 : ℝ) (157/1024 : ℝ) (167264769673/200000000000 : ℝ) (1009702126851/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0608; no trusted numerical premise.
theorem cover7_leaf0608_exp_radius : (199451437274861869/200000000000000000 : ℝ) ≤ Real.exp ((-45/2048 : ℝ)/8) ∧ Real.exp ((-45/2048 : ℝ)/8) ≤ (498628593187154673/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-45/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0608_exp_lower : (918115751812813669/1000000000000000000 : ℝ) ≤ Real.exp ((-683454440089/1000000000000 : ℝ)/8) ∧ Real.exp ((-683454440089/1000000000000 : ℝ)/8) ≤ (91811575181281367/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683454440089/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0608_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009739867219/500000000000 : ℝ) ≤ 4*Real.exp (157/1024 : ℝ)*Real.exp (-mu (radius 7 (315/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009739867219/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (315/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0608_exp_radius
  have hrNumeric : (978266984173/1000000000000 : ℝ) ≤ Real.exp (-45/2048 : ℝ) ∧ Real.exp (-45/2048 : ℝ) ≤ (489133492087/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (978266984173/1000000000000 : ℝ) ≤ (radius 7 (315/2048 : ℝ)) ∧ (radius 7 (315/2048 : ℝ)) ≤ (489133492087/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (315/2048 : ℝ)) (978266984173/1000000000000 : ℝ) (489133492087/500000000000 : ℝ) (41469848167/200000000000 : ℝ) (207349240841/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (315/2048 : ℝ)) (978266984173/1000000000000 : ℝ) (489133492087/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (315/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (978266984173/1000000000000 : ℝ) (489133492087/500000000000 : ℝ) (494566746043/500000000000 : ℝ) (989133492087/1000000000000 : ℝ) (123634225147/125000000000 : ℝ) (989073801177/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (315/2048 : ℝ)) 1 (494566746043/500000000000 : ℝ) (989133492087/1000000000000 : ℝ) (123634225147/125000000000 : ℝ) (989073801177/1000000000000 : ℝ) (989103646631/1000000000000 : ℝ) (123637955829/125000000000 : ℝ) (49455182309/50000000000 : ℝ) (494551823091/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (315/2048 : ℝ)) 2 (989103646631/1000000000000 : ℝ) (123637955829/125000000000 : ℝ) (49455182309/50000000000 : ℝ) (494551823091/500000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (315/2048 : ℝ)) 3 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (315/2048 : ℝ)) 4 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (315/2048 : ℝ)) 5 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (315/2048 : ℝ)) 6 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (315/2048 : ℝ)) 7 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (315/2048 : ℝ))) (41469848167/200000000000 : ℝ) (207349240841/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (315/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (41469848167/200000000000 : ℝ) (207349240841/1000000000000 : ℝ) (603674620417/1000000000000 : ℝ) (603674620421/1000000000000 : ℝ) (455356169207/1000000000000 : ℝ) (227678084607/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (315/2048 : ℝ))) 1 (603674620417/1000000000000 : ℝ) (603674620421/1000000000000 : ℝ) (455356169207/1000000000000 : ℝ) (227678084607/500000000000 : ℝ) (132378848703/250000000000 : ℝ) (264757697409/500000000000 : ℝ) (20971865443/40000000000 : ℝ) (262148318041/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (315/2048 : ℝ))) 2 (132378848703/250000000000 : ℝ) (264757697409/500000000000 : ℝ) (20971865443/40000000000 : ℝ) (262148318041/500000000000 : ℝ) (526906015443/1000000000000 : ℝ) (10538120309/20000000000 : ℝ) (526899554231/1000000000000 : ℝ) (526899554239/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (315/2048 : ℝ))) 3 (526906015443/1000000000000 : ℝ) (10538120309/20000000000 : ℝ) (526899554231/1000000000000 : ℝ) (526899554239/1000000000000 : ℝ) (526902784837/1000000000000 : ℝ) (105380556969/200000000000 : ℝ) (526902784827/1000000000000 : ℝ) (105380556967/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (315/2048 : ℝ))) 4 (526902784837/1000000000000 : ℝ) (105380556969/200000000000 : ℝ) (526902784827/1000000000000 : ℝ) (105380556967/200000000000 : ℝ) (8232856013/15625000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (315/2048 : ℝ))) 5 (8232856013/15625000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (315/2048 : ℝ))) 6 (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (315/2048 : ℝ))) 7 (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (315/2048 : ℝ)) hmem 8 (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (315/2048 : ℝ))) hcmem 8 (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (315/2048 : ℝ)) (197820729281/200000000000 : ℝ) (989103646407/1000000000000 : ℝ) (526902784831/1000000000000 : ℝ) (13172569621/25000000000 : ℝ) (209193688143/250000000000 : ℝ) (836774752589/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0608_exp_lower
  have heNumeric : (1009739867219/500000000000 : ℝ)/4 ≤ Real.exp (-683454440089/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009739867219/500000000000 : ℝ)/4 ≤ Real.exp ((157/1024 : ℝ)-(836774752589/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (157/1024 : ℝ) (315/2048 : ℝ) (836774752589/1000000000000 : ℝ) (1009739867219/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0609; no trusted numerical premise.
theorem cover7_leaf0609_exp_radius : (99724849101961931/100000000000000000 : ℝ) ≤ Real.exp ((-79/3584 : ℝ)/8) ∧ Real.exp ((-79/3584 : ℝ)/8) ≤ (997248491019619311/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-79/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0609_exp_lower : (459060074918885597/500000000000000000 : ℝ) ≤ Real.exp ((-341708058999/500000000000 : ℝ)/8) ∧ Real.exp ((-341708058999/500000000000 : ℝ)/8) ≤ (183624029967554239/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341708058999/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0609_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019557126607/1000000000000 : ℝ) ≤ 4*Real.exp (315/2048 : ℝ)*Real.exp (-mu (radius 7 (79/512 : ℝ))) ∧ (2019/1000 : ℝ) < (2019557126607/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (79/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0609_exp_radius
  have hrNumeric : (978198748063/1000000000000 : ℝ) ≤ Real.exp (-79/3584 : ℝ) ∧ Real.exp (-79/3584 : ℝ) ≤ (30568710877/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (978198748063/1000000000000 : ℝ) ≤ (radius 7 (79/512 : ℝ)) ∧ (radius 7 (79/512 : ℝ)) ≤ (30568710877/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (79/512 : ℝ)) (978198748063/1000000000000 : ℝ) (30568710877/31250000000 : ℝ) (162242903/781250000 : ℝ) (103835457923/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (79/512 : ℝ)) (978198748063/1000000000000 : ℝ) (30568710877/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (79/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (978198748063/1000000000000 : ℝ) (30568710877/31250000000 : ℝ) (989099374031/1000000000000 : ℝ) (61818710877/62500000000 : ℝ) (49451965281/50000000000 : ℝ) (494519652811/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (79/512 : ℝ)) 1 (989099374031/1000000000000 : ℝ) (61818710877/62500000000 : ℝ) (49451965281/50000000000 : ℝ) (494519652811/500000000000 : ℝ) (39562773593/40000000000 : ℝ) (989069339827/1000000000000 : ℝ) (989069339369/1000000000000 : ℝ) (989069339371/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (79/512 : ℝ)) 2 (39562773593/40000000000 : ℝ) (989069339827/1000000000000 : ℝ) (989069339369/1000000000000 : ℝ) (989069339371/1000000000000 : ℝ) (989069339597/1000000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (79/512 : ℝ)) 3 (989069339597/1000000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (79/512 : ℝ)) 4 (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (79/512 : ℝ)) 5 (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (79/512 : ℝ)) 6 (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (79/512 : ℝ)) 7 (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (79/512 : ℝ))) (162242903/781250000 : ℝ) (103835457923/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (79/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (162242903/781250000 : ℝ) (103835457923/500000000000 : ℝ) (943492903/1562500000 : ℝ) (603835457923/1000000000000 : ℝ) (28481827803/62500000000 : ℝ) (91141848971/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (79/512 : ℝ))) 1 (943492903/1562500000 : ℝ) (603835457923/1000000000000 : ℝ) (28481827803/62500000000 : ℝ) (91141848971/200000000000 : ℝ) (66221543923/125000000000 : ℝ) (529772351389/1000000000000 : ℝ) (1639280403/3125000000 : ℝ) (262284864483/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (79/512 : ℝ))) 2 (66221543923/125000000000 : ℝ) (529772351389/1000000000000 : ℝ) (1639280403/3125000000 : ℝ) (262284864483/500000000000 : ℝ) (131792760043/250000000000 : ℝ) (263585520089/500000000000 : ℝ) (527164622083/1000000000000 : ℝ) (527164622089/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (79/512 : ℝ))) 3 (131792760043/250000000000 : ℝ) (263585520089/500000000000 : ℝ) (527164622083/1000000000000 : ℝ) (527164622089/1000000000000 : ℝ) (527167831127/1000000000000 : ℝ) (263583915567/500000000000 : ℝ) (527167831117/1000000000000 : ℝ) (131791957781/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (79/512 : ℝ))) 4 (527167831127/1000000000000 : ℝ) (263583915567/500000000000 : ℝ) (527167831117/1000000000000 : ℝ) (131791957781/250000000000 : ℝ) (263583915561/500000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (79/512 : ℝ))) 5 (263583915561/500000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (79/512 : ℝ))) 6 (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (79/512 : ℝ))) 7 (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (79/512 : ℝ)) hmem 8 (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (79/512 : ℝ))) hcmem 8 (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (79/512 : ℝ)) (247267334899/250000000000 : ℝ) (989069339599/1000000000000 : ℝ) (527167831121/1000000000000 : ℝ) (527167831129/1000000000000 : ℝ) (209306177933/250000000000 : ℝ) (209306177937/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0609_exp_lower
  have heNumeric : (2019557126607/1000000000000 : ℝ)/4 ≤ Real.exp (-341708058999/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019557126607/1000000000000 : ℝ)/4 ≤ Real.exp ((315/2048 : ℝ)-(209306177937/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (315/2048 : ℝ) (79/512 : ℝ) (209306177937/250000000000 : ℝ) (2019557126607/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0610; no trusted numerical premise.
theorem cover7_leaf0610_exp_radius : (498619897870373211/500000000000000000 : ℝ) ≤ Real.exp ((-317/14336 : ℝ)/8) ∧ Real.exp ((-317/14336 : ℝ)/8) ≤ (997239795740746423/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-317/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0610_exp_lower : (918124655746681397/1000000000000000000 : ℝ) ≤ Real.exp ((-683376856053/1000000000000 : ℝ)/8) ∧ Real.exp ((-683376856053/1000000000000 : ℝ)/8) ≤ (459062327873340699/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683376856053/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0610_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (31556819061/15625000000 : ℝ) ≤ 4*Real.exp (79/512 : ℝ)*Real.exp (-mu (radius 7 (317/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (31556819061/15625000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (317/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0610_exp_radius
  have hrNumeric : (978130516713/1000000000000 : ℝ) ≤ Real.exp (-317/14336 : ℝ) ∧ Real.exp (-317/14336 : ℝ) ≤ (489065258357/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (978130516713/1000000000000 : ℝ) ≤ (radius 7 (317/2048 : ℝ)) ∧ (radius 7 (317/2048 : ℝ)) ≤ (489065258357/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (317/2048 : ℝ)) (978130516713/1000000000000 : ℝ) (489065258357/500000000000 : ℝ) (10399602429/50000000000 : ℝ) (103996024293/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (317/2048 : ℝ)) (978130516713/1000000000000 : ℝ) (489065258357/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (317/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (978130516713/1000000000000 : ℝ) (489065258357/500000000000 : ℝ) (247266314589/250000000000 : ℝ) (989065258357/1000000000000 : ℝ) (247251202817/250000000000 : ℝ) (98900481127/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (317/2048 : ℝ)) 1 (247266314589/250000000000 : ℝ) (989065258357/1000000000000 : ℝ) (247251202817/250000000000 : ℝ) (98900481127/100000000000 : ℝ) (247258758703/250000000000 : ℝ) (494517517407/500000000000 : ℝ) (19780700687/20000000000 : ℝ) (61814689647/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (317/2048 : ℝ)) 2 (247258758703/250000000000 : ℝ) (494517517407/500000000000 : ℝ) (19780700687/20000000000 : ℝ) (61814689647/62500000000 : ℝ) (989035034581/1000000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (317/2048 : ℝ)) 3 (989035034581/1000000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (317/2048 : ℝ)) 4 (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (317/2048 : ℝ)) 5 (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (317/2048 : ℝ)) 6 (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (317/2048 : ℝ)) 7 (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (317/2048 : ℝ))) (10399602429/50000000000 : ℝ) (103996024293/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (317/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (10399602429/50000000000 : ℝ) (103996024293/500000000000 : ℝ) (60399602429/100000000000 : ℝ) (603996024293/1000000000000 : ℝ) (91212290527/200000000000 : ℝ) (456061452643/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (317/2048 : ℝ))) 1 (60399602429/100000000000 : ℝ) (603996024293/1000000000000 : ℝ) (91212290527/200000000000 : ℝ) (456061452643/1000000000000 : ℝ) (265014369231/500000000000 : ℝ) (132507184617/250000000000 : ℝ) (262421085387/500000000000 : ℝ) (524842170781/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (317/2048 : ℝ))) 2 (265014369231/500000000000 : ℝ) (132507184617/250000000000 : ℝ) (262421085387/500000000000 : ℝ) (524842170781/1000000000000 : ℝ) (263717727309/500000000000 : ℝ) (4219483637/8000000000 : ℝ) (527429079277/1000000000000 : ℝ) (131857269821/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (317/2048 : ℝ))) 3 (263717727309/500000000000 : ℝ) (4219483637/8000000000 : ℝ) (527429079277/1000000000000 : ℝ) (131857269821/250000000000 : ℝ) (527432266947/1000000000000 : ℝ) (105486453391/200000000000 : ℝ) (527432266937/1000000000000 : ℝ) (105486453389/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (317/2048 : ℝ))) 4 (527432266947/1000000000000 : ℝ) (105486453391/200000000000 : ℝ) (527432266937/1000000000000 : ℝ) (105486453389/200000000000 : ℝ) (263716133471/500000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (317/2048 : ℝ))) 5 (263716133471/500000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (317/2048 : ℝ))) 6 (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (317/2048 : ℝ))) 7 (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (317/2048 : ℝ)) hmem 8 (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (317/2048 : ℝ))) hcmem 8 (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (317/2048 : ℝ)) (49451751729/50000000000 : ℝ) (989035034583/1000000000000 : ℝ) (527432266941/1000000000000 : ℝ) (10548645339/20000000000 : ℝ) (167534746207/200000000000 : ℝ) (837673731053/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0610_exp_lower
  have heNumeric : (31556819061/15625000000 : ℝ)/4 ≤ Real.exp (-683376856053/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (31556819061/15625000000 : ℝ)/4 ≤ Real.exp ((79/512 : ℝ)-(837673731053/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (79/512 : ℝ) (317/2048 : ℝ) (837673731053/1000000000000 : ℝ) (31556819061/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0611; no trusted numerical premise.
theorem cover7_leaf0611_exp_radius : (997231100537690017/1000000000000000000 : ℝ) ≤ Real.exp ((-159/7168 : ℝ)/8) ∧ Real.exp ((-159/7168 : ℝ)/8) ≤ (498615550268845009/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-159/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0611_exp_lower : (459064634473723567/500000000000000000 : ℝ) ≤ Real.exp ((-683336659427/1000000000000 : ℝ)/8) ∧ Real.exp ((-683336659427/1000000000000 : ℝ)/8) ≤ (183625853789489427/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683336659427/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0611_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009858802053/500000000000 : ℝ) ≤ 4*Real.exp (317/2048 : ℝ)*Real.exp (-mu (radius 7 (159/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (1009858802053/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (159/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0611_exp_radius
  have hrNumeric : (978062290123/1000000000000 : ℝ) ≤ Real.exp (-159/7168 : ℝ) ∧ Real.exp (-159/7168 : ℝ) ≤ (244515572531/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (978062290123/1000000000000 : ℝ) ≤ (radius 7 (159/1024 : ℝ)) ∧ (radius 7 (159/1024 : ℝ)) ≤ (244515572531/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (159/1024 : ℝ)) (978062290123/1000000000000 : ℝ) (244515572531/250000000000 : ℝ) (6509770049/31250000000 : ℝ) (104156320787/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (159/1024 : ℝ)) (978062290123/1000000000000 : ℝ) (244515572531/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (159/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (978062290123/1000000000000 : ℝ) (244515572531/250000000000 : ℝ) (989031145061/1000000000000 : ℝ) (494515572531/500000000000 : ℝ) (24724257953/25000000000 : ℝ) (988970318121/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (159/1024 : ℝ)) 1 (989031145061/1000000000000 : ℝ) (494515572531/500000000000 : ℝ) (24724257953/25000000000 : ℝ) (988970318121/1000000000000 : ℝ) (98900073159/100000000000 : ℝ) (123625091449/125000000000 : ℝ) (494500365561/500000000000 : ℝ) (247250182781/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (159/1024 : ℝ)) 2 (98900073159/100000000000 : ℝ) (123625091449/125000000000 : ℝ) (494500365561/500000000000 : ℝ) (247250182781/250000000000 : ℝ) (247250182839/250000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (159/1024 : ℝ)) 3 (247250182839/250000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (159/1024 : ℝ)) 4 (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (159/1024 : ℝ)) 5 (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (159/1024 : ℝ)) 6 (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (159/1024 : ℝ)) 7 (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (159/1024 : ℝ))) (6509770049/31250000000 : ℝ) (104156320787/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (159/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (6509770049/31250000000 : ℝ) (104156320787/500000000000 : ℝ) (37759770049/62500000000 : ℝ) (604156320787/1000000000000 : ℝ) (456412797331/1000000000000 : ℝ) (456412797339/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (159/1024 : ℝ))) 1 (37759770049/62500000000 : ℝ) (604156320787/1000000000000 : ℝ) (456412797331/1000000000000 : ℝ) (456412797339/1000000000000 : ℝ) (530284559057/1000000000000 : ℝ) (530284559063/1000000000000 : ℝ) (131278491287/250000000000 : ℝ) (105022793031/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (159/1024 : ℝ))) 2 (530284559057/1000000000000 : ℝ) (530284559063/1000000000000 : ℝ) (131278491287/250000000000 : ℝ) (105022793031/200000000000 : ℝ) (263849631051/500000000000 : ℝ) (527699262109/1000000000000 : ℝ) (263846464569/500000000000 : ℝ) (263846464573/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (159/1024 : ℝ))) 3 (263849631051/500000000000 : ℝ) (527699262109/1000000000000 : ℝ) (263846464569/500000000000 : ℝ) (263846464573/500000000000 : ℝ) (26384804781/50000000000 : ℝ) (131924023907/250000000000 : ℝ) (52769609561/100000000000 : ℝ) (263848047809/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (159/1024 : ℝ))) 4 (26384804781/50000000000 : ℝ) (131924023907/250000000000 : ℝ) (52769609561/100000000000 : ℝ) (263848047809/500000000000 : ℝ) (105539219123/200000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (159/1024 : ℝ))) 5 (105539219123/200000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (159/1024 : ℝ))) 6 (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (159/1024 : ℝ))) 7 (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (159/1024 : ℝ)) hmem 8 (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (159/1024 : ℝ))) hcmem 8 (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (159/1024 : ℝ)) (197800146271/200000000000 : ℝ) (494500365679/500000000000 : ℝ) (263848047807/500000000000 : ℝ) (527696095623/1000000000000 : ℝ) (838121815659/1000000000000 : ℝ) (838121815677/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0611_exp_lower
  have heNumeric : (1009858802053/500000000000 : ℝ)/4 ≤ Real.exp (-683336659427/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009858802053/500000000000 : ℝ)/4 ≤ Real.exp ((317/2048 : ℝ)-(838121815677/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (317/2048 : ℝ) (159/1024 : ℝ) (838121815677/1000000000000 : ℝ) (1009858802053/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0612; no trusted numerical premise.
theorem cover7_leaf0612_exp_radius : (249305601352612359/250000000000000000 : ℝ) ≤ Real.exp ((-319/14336 : ℝ)/8) ∧ Real.exp ((-319/14336 : ℝ)/8) ≤ (997222405410449437/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-319/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0612_exp_lower : (918133988851325321/1000000000000000000 : ℝ) ≤ Real.exp ((-42705970829/62500000000 : ℝ)/8) ∧ Real.exp ((-42705970829/62500000000 : ℝ)/8) ≤ (459066994425662661/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42705970829/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0612_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019800669049/1000000000000 : ℝ) ≤ 4*Real.exp (159/1024 : ℝ)*Real.exp (-mu (radius 7 (319/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (2019800669049/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (319/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0612_exp_radius
  have hrNumeric : (977994068291/1000000000000 : ℝ) ≤ Real.exp (-319/14336 : ℝ) ∧ Real.exp (-319/14336 : ℝ) ≤ (244498517073/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (977994068291/1000000000000 : ℝ) ≤ (radius 7 (319/2048 : ℝ)) ∧ (radius 7 (319/2048 : ℝ)) ≤ (244498517073/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (319/2048 : ℝ)) (977994068291/1000000000000 : ℝ) (244498517073/250000000000 : ℝ) (208632697307/1000000000000 : ℝ) (6519771791/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (319/2048 : ℝ)) (977994068291/1000000000000 : ℝ) (244498517073/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (319/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (977994068291/1000000000000 : ℝ) (244498517073/250000000000 : ℝ) (197799406829/200000000000 : ℝ) (494498517073/500000000000 : ℝ) (494467913087/500000000000 : ℝ) (39557433047/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (319/2048 : ℝ)) 1 (197799406829/200000000000 : ℝ) (494498517073/500000000000 : ℝ) (494467913087/500000000000 : ℝ) (39557433047/40000000000 : ℝ) (988966430159/1000000000000 : ℝ) (988966430161/1000000000000 : ℝ) (197793285937/200000000000 : ℝ) (988966429687/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (319/2048 : ℝ)) 2 (988966430159/1000000000000 : ℝ) (988966430161/1000000000000 : ℝ) (197793285937/200000000000 : ℝ) (988966429687/1000000000000 : ℝ) (494483214961/500000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (319/2048 : ℝ)) 3 (494483214961/500000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (319/2048 : ℝ)) 4 (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (319/2048 : ℝ)) 5 (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (319/2048 : ℝ)) 6 (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (319/2048 : ℝ)) 7 (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (319/2048 : ℝ))) (208632697307/1000000000000 : ℝ) (6519771791/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (319/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (208632697307/1000000000000 : ℝ) (6519771791/31250000000 : ℝ) (604316348653/1000000000000 : ℝ) (37769771791/62500000000 : ℝ) (456763283667/1000000000000 : ℝ) (228381641837/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (319/2048 : ℝ))) 1 (604316348653/1000000000000 : ℝ) (37769771791/62500000000 : ℝ) (456763283667/1000000000000 : ℝ) (228381641837/500000000000 : ℝ) (3315873851/6250000000 : ℝ) (106107963233/200000000000 : ℝ) (262692557843/500000000000 : ℝ) (131346278923/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (319/2048 : ℝ))) 2 (3315873851/6250000000 : ℝ) (106107963233/200000000000 : ℝ) (262692557843/500000000000 : ℝ) (131346278923/250000000000 : ℝ) (527962465923/1000000000000 : ℝ) (527962465929/1000000000000 : ℝ) (52795617497/100000000000 : ℝ) (4124657617/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (319/2048 : ℝ))) 3 (527962465923/1000000000000 : ℝ) (527962465929/1000000000000 : ℝ) (52795617497/100000000000 : ℝ) (4124657617/7812500000 : ℝ) (263979660223/500000000000 : ℝ) (527959320453/1000000000000 : ℝ) (527959320437/1000000000000 : ℝ) (131989830111/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (319/2048 : ℝ))) 4 (263979660223/500000000000 : ℝ) (527959320453/1000000000000 : ℝ) (527959320437/1000000000000 : ℝ) (131989830111/250000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (319/2048 : ℝ))) 5 (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (319/2048 : ℝ))) 6 (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (319/2048 : ℝ))) 7 (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (319/2048 : ℝ)) hmem 8 (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (319/2048 : ℝ))) hcmem 8 (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (319/2048 : ℝ)) (988966429921/1000000000000 : ℝ) (247241607481/250000000000 : ℝ) (527959320441/1000000000000 : ℝ) (527959320449/1000000000000 : ℝ) (209642242687/250000000000 : ℝ) (209642242691/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0612_exp_lower
  have heNumeric : (2019800669049/1000000000000 : ℝ)/4 ≤ Real.exp (-42705970829/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019800669049/1000000000000 : ℝ)/4 ≤ Real.exp ((159/1024 : ℝ)-(209642242691/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (159/1024 : ℝ) (319/2048 : ℝ) (209642242691/250000000000 : ℝ) (2019800669049/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0613; no trusted numerical premise.
theorem cover7_leaf0613_exp_radius : (498606855179512009/500000000000000000 : ℝ) ≤ Real.exp ((-5/224 : ℝ)/8) ∧ Real.exp ((-5/224 : ℝ)/8) ≤ (997213710359024019/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5/224 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0613_exp_lower : (18362776297554931/20000000000000000 : ℝ) ≤ Real.exp ((-683253482637/1000000000000 : ℝ)/8) ∧ Real.exp ((-683253482637/1000000000000 : ℝ)/8) ≤ (918138814877746551/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683253482637/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0613_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25248570059/12500000000 : ℝ) ≤ 4*Real.exp (319/2048 : ℝ)*Real.exp (-mu (radius 7 (5/32 : ℝ))) ∧ (2019/1000 : ℝ) < (25248570059/12500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (5/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0613_exp_radius
  have hrNumeric : (488962925609/500000000000 : ℝ) ≤ Real.exp (-5/224 : ℝ) ∧ Real.exp (-5/224 : ℝ) ≤ (977925851219/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (488962925609/500000000000 : ℝ) ≤ (radius 7 (5/32 : ℝ)) ∧ (radius 7 (5/32 : ℝ)) ≤ (977925851219/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (5/32 : ℝ)) (488962925609/500000000000 : ℝ) (977925851219/1000000000000 : ℝ) (26119027283/125000000000 : ℝ) (20895221827/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (5/32 : ℝ)) (488962925609/500000000000 : ℝ) (977925851219/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (5/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (488962925609/500000000000 : ℝ) (977925851219/1000000000000 : ℝ) (988962925609/1000000000000 : ℝ) (98896292561/100000000000 : ℝ) (988901335431/1000000000000 : ℝ) (123612666929/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (5/32 : ℝ)) 1 (988962925609/1000000000000 : ℝ) (98896292561/100000000000 : ℝ) (988901335431/1000000000000 : ℝ) (123612666929/125000000000 : ℝ) (24723303263/25000000000 : ℝ) (988932130521/1000000000000 : ℝ) (24723303251/25000000000 : ℝ) (494466065021/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (5/32 : ℝ)) 2 (24723303263/25000000000 : ℝ) (988932130521/1000000000000 : ℝ) (24723303251/25000000000 : ℝ) (494466065021/500000000000 : ℝ) (24723303257/25000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (5/32 : ℝ)) 3 (24723303257/25000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (5/32 : ℝ)) 4 (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (5/32 : ℝ)) 5 (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (5/32 : ℝ)) 6 (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (5/32 : ℝ)) 7 (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (5/32 : ℝ))) (26119027283/125000000000 : ℝ) (20895221827/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (5/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (26119027283/125000000000 : ℝ) (20895221827/100000000000 : ℝ) (151119027283/250000000000 : ℝ) (120895221827/200000000000 : ℝ) (457112916317/1000000000000 : ℝ) (114278229081/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (5/32 : ℝ))) 1 (151119027283/250000000000 : ℝ) (120895221827/200000000000 : ℝ) (457112916317/1000000000000 : ℝ) (114278229081/250000000000 : ℝ) (132698628181/250000000000 : ℝ) (53079451273/100000000000 : ℝ) (262827812973/500000000000 : ℝ) (16426738311/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (5/32 : ℝ))) 2 (132698628181/250000000000 : ℝ) (53079451273/100000000000 : ℝ) (262827812973/500000000000 : ℝ) (16426738311/31250000000 : ℝ) (105645013867/200000000000 : ℝ) (528225069341/1000000000000 : ℝ) (52821882003/100000000000 : ℝ) (528218820037/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (5/32 : ℝ))) 3 (105645013867/200000000000 : ℝ) (528225069341/1000000000000 : ℝ) (52821882003/100000000000 : ℝ) (528218820037/1000000000000 : ℝ) (264110972341/500000000000 : ℝ) (528221944689/1000000000000 : ℝ) (528221944673/1000000000000 : ℝ) (13205548617/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (5/32 : ℝ))) 4 (264110972341/500000000000 : ℝ) (528221944689/1000000000000 : ℝ) (528221944673/1000000000000 : ℝ) (13205548617/25000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (5/32 : ℝ))) 5 (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (5/32 : ℝ))) 6 (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (5/32 : ℝ))) 7 (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (5/32 : ℝ)) hmem 8 (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (5/32 : ℝ))) hcmem 8 (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (5/32 : ℝ)) (988932130279/1000000000000 : ℝ) (494466065141/500000000000 : ℝ) (528221944677/1000000000000 : ℝ) (105644388937/200000000000 : ℝ) (839015201371/1000000000000 : ℝ) (839015201387/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0613_exp_lower
  have heNumeric : (25248570059/12500000000 : ℝ)/4 ≤ Real.exp (-683253482637/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25248570059/12500000000 : ℝ)/4 ≤ Real.exp ((319/2048 : ℝ)-(839015201387/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (319/2048 : ℝ) (5/32 : ℝ) (839015201387/1000000000000 : ℝ) (25248570059/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0614; no trusted numerical premise.
theorem cover7_leaf0614_exp_radius : (997196320483616023/1000000000000000000 : ℝ) ≤ Real.exp ((-23/1024 : ℝ)/8) ∧ Real.exp ((-23/1024 : ℝ)/8) ≤ (124649540060452003/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-23/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0614_exp_lower : (183618549069776737/200000000000000000 : ℝ) ≤ Real.exp ((-85456863673/125000000000 : ℝ)/8) ∧ Real.exp ((-85456863673/125000000000 : ℝ)/8) ≤ (459046372674441843/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85456863673/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0614_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252384366417/125000000000 : ℝ) ≤ 4*Real.exp (5/32 : ℝ)*Real.exp (-mu (radius 7 (161/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (252384366417/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (161/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0614_exp_radius
  have hrNumeric : (977789431347/1000000000000 : ℝ) ≤ Real.exp (-23/1024 : ℝ) ∧ Real.exp (-23/1024 : ℝ) ≤ (244447357837/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (977789431347/1000000000000 : ℝ) ≤ (radius 7 (161/1024 : ℝ)) ∧ (radius 7 (161/1024 : ℝ)) ≤ (244447357837/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (161/1024 : ℝ)) (977789431347/1000000000000 : ℝ) (244447357837/250000000000 : ℝ) (104794832821/500000000000 : ℝ) (13099354103/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (161/1024 : ℝ)) (977789431347/1000000000000 : ℝ) (244447357837/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (161/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (977789431347/1000000000000 : ℝ) (244447357837/250000000000 : ℝ) (988894715673/1000000000000 : ℝ) (494447357837/500000000000 : ℝ) (494416178777/500000000000 : ℝ) (247208089389/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (161/1024 : ℝ)) 1 (988894715673/1000000000000 : ℝ) (494447357837/500000000000 : ℝ) (494416178777/500000000000 : ℝ) (247208089389/250000000000 : ℝ) (988863536613/1000000000000 : ℝ) (197772707323/200000000000 : ℝ) (988863536121/1000000000000 : ℝ) (247215884031/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (161/1024 : ℝ)) 2 (988863536613/1000000000000 : ℝ) (197772707323/200000000000 : ℝ) (988863536121/1000000000000 : ℝ) (247215884031/250000000000 : ℝ) (988863536367/1000000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (161/1024 : ℝ)) 3 (988863536367/1000000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (161/1024 : ℝ)) 4 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (161/1024 : ℝ)) 5 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (161/1024 : ℝ)) 6 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (161/1024 : ℝ)) 7 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (161/1024 : ℝ))) (104794832821/500000000000 : ℝ) (13099354103/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (161/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (104794832821/500000000000 : ℝ) (13099354103/62500000000 : ℝ) (604794832821/1000000000000 : ℝ) (75599354103/125000000000 : ℝ) (28613102443/62500000000 : ℝ) (91561927819/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (161/1024 : ℝ))) 1 (604794832821/1000000000000 : ℝ) (75599354103/125000000000 : ℝ) (28613102443/62500000000 : ℝ) (91561927819/200000000000 : ℝ) (265651117977/500000000000 : ℝ) (13282555899/25000000000 : ℝ) (105238947949/200000000000 : ℝ) (65774342469/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (161/1024 : ℝ))) 2 (265651117977/500000000000 : ℝ) (13282555899/25000000000 : ℝ) (105238947949/200000000000 : ℝ) (65774342469/125000000000 : ℝ) (528748487849/1000000000000 : ℝ) (33046780491/62500000000 : ℝ) (52874232077/100000000000 : ℝ) (528742320777/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (161/1024 : ℝ))) 3 (528748487849/1000000000000 : ℝ) (33046780491/62500000000 : ℝ) (52874232077/100000000000 : ℝ) (528742320777/1000000000000 : ℝ) (528745404309/1000000000000 : ℝ) (528745404317/1000000000000 : ℝ) (5287454043/10000000000 : ℝ) (132186351077/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (161/1024 : ℝ))) 4 (528745404309/1000000000000 : ℝ) (528745404317/1000000000000 : ℝ) (5287454043/10000000000 : ℝ) (132186351077/250000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (161/1024 : ℝ))) 5 (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (161/1024 : ℝ))) 6 (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (161/1024 : ℝ))) 7 (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (161/1024 : ℝ)) hmem 8 (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (161/1024 : ℝ))) hcmem 8 (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (161/1024 : ℝ)) (494431768183/500000000000 : ℝ) (98886353637/100000000000 : ℝ) (33046587769/62500000000 : ℝ) (528745404313/1000000000000 : ℝ) (419952454683/500000000000 : ℝ) (104988113673/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0614_exp_lower
  have heNumeric : (252384366417/125000000000 : ℝ)/4 ≤ Real.exp (-85456863673/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252384366417/125000000000 : ℝ)/4 ≤ Real.exp ((5/32 : ℝ)-(104988113673/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (5/32 : ℝ) (161/1024 : ℝ) (104988113673/125000000000 : ℝ) (252384366417/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0615; no trusted numerical premise.
theorem cover7_leaf0615_exp_radius : (199435786182292149/200000000000000000 : ℝ) ≤ Real.exp ((-81/3584 : ℝ)/8) ∧ Real.exp ((-81/3584 : ℝ)/8) ≤ (498589465455730373/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-81/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0615_exp_lower : (918103130457317817/1000000000000000000 : ℝ) ≤ Real.exp ((-170891104251/250000000000 : ℝ)/8) ∧ Real.exp ((-170891104251/250000000000 : ℝ)/8) ≤ (459051565228658909/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170891104251/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0615_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019257650499/1000000000000 : ℝ) ≤ 4*Real.exp (161/1024 : ℝ)*Real.exp (-mu (radius 7 (81/512 : ℝ))) ∧ (2019/1000 : ℝ) < (2019257650499/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (81/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0615_exp_radius
  have hrNumeric : (195530606101/200000000000 : ℝ) ≤ Real.exp (-81/3584 : ℝ) ∧ Real.exp (-81/3584 : ℝ) ≤ (488826515253/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (195530606101/200000000000 : ℝ) ≤ (radius 7 (81/512 : ℝ)) ∧ (radius 7 (81/512 : ℝ)) ≤ (488826515253/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (81/512 : ℝ)) (195530606101/200000000000 : ℝ) (488826515253/500000000000 : ℝ) (210225003133/1000000000000 : ℝ) (210225003139/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (81/512 : ℝ)) (195530606101/200000000000 : ℝ) (488826515253/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (81/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (195530606101/200000000000 : ℝ) (488826515253/500000000000 : ℝ) (247206628813/250000000000 : ℝ) (988826515253/1000000000000 : ℝ) (123595423061/125000000000 : ℝ) (988763384489/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (81/512 : ℝ)) 1 (247206628813/250000000000 : ℝ) (988826515253/1000000000000 : ℝ) (123595423061/125000000000 : ℝ) (988763384489/1000000000000 : ℝ) (98879494987/100000000000 : ℝ) (988794949871/1000000000000 : ℝ) (494397474683/500000000000 : ℝ) (123599368671/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (81/512 : ℝ)) 2 (98879494987/100000000000 : ℝ) (988794949871/1000000000000 : ℝ) (494397474683/500000000000 : ℝ) (123599368671/125000000000 : ℝ) (494397474809/500000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (81/512 : ℝ)) 3 (494397474809/500000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (81/512 : ℝ)) 4 (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (81/512 : ℝ)) 5 (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (81/512 : ℝ)) 6 (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (81/512 : ℝ)) 7 (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (81/512 : ℝ))) (210225003133/1000000000000 : ℝ) (210225003139/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (81/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (210225003133/1000000000000 : ℝ) (210225003139/1000000000000 : ℝ) (302556250783/500000000000 : ℝ) (60511250157/100000000000 : ℝ) (114625750579/250000000000 : ℝ) (458503002323/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (81/512 : ℝ))) 1 (302556250783/500000000000 : ℝ) (60511250157/100000000000 : ℝ) (114625750579/250000000000 : ℝ) (458503002323/1000000000000 : ℝ) (531807751941/1000000000000 : ℝ) (531807751947/1000000000000 : ℝ) (8230177101/15625000000 : ℝ) (526731334471/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (81/512 : ℝ))) 2 (531807751941/1000000000000 : ℝ) (531807751947/1000000000000 : ℝ) (8230177101/15625000000 : ℝ) (526731334471/1000000000000 : ℝ) (264634771601/500000000000 : ℝ) (529269543209/1000000000000 : ℝ) (105852691389/200000000000 : ℝ) (529263456953/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (81/512 : ℝ))) 3 (264634771601/500000000000 : ℝ) (529269543209/1000000000000 : ℝ) (105852691389/200000000000 : ℝ) (529263456953/1000000000000 : ℝ) (529266500073/1000000000000 : ℝ) (529266500081/1000000000000 : ℝ) (16539578127/31250000000 : ℝ) (529266500073/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (81/512 : ℝ))) 4 (529266500073/1000000000000 : ℝ) (529266500081/1000000000000 : ℝ) (16539578127/31250000000 : ℝ) (529266500073/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (81/512 : ℝ))) 5 (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (81/512 : ℝ))) 6 (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (81/512 : ℝ))) 7 (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (81/512 : ℝ)) hmem 8 (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (81/512 : ℝ))) hcmem 8 (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (81/512 : ℝ)) (988794949617/1000000000000 : ℝ) (49439747481/50000000000 : ℝ) (132316625017/250000000000 : ℝ) (529266500077/1000000000000 : ℝ) (420395489743/500000000000 : ℝ) (52549436219/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0615_exp_lower
  have heNumeric : (2019257650499/1000000000000 : ℝ)/4 ≤ Real.exp (-170891104251/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019257650499/1000000000000 : ℝ)/4 ≤ Real.exp ((161/1024 : ℝ)-(52549436219/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (161/1024 : ℝ) (81/512 : ℝ) (52549436219/62500000000 : ℝ) (2019257650499/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0616; no trusted numerical premise.
theorem cover7_leaf0616_exp_radius : (199432308328510579/200000000000000000 : ℝ) ≤ Real.exp ((-163/7168 : ℝ)/8) ∧ Real.exp ((-163/7168 : ℝ)/8) ≤ (15580649088164889/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-163/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0616_exp_lower : (183622785738074031/200000000000000000 : ℝ) ≤ Real.exp ((-683470325879/1000000000000 : ℝ)/8) ∧ Real.exp ((-683470325879/1000000000000 : ℝ)/8) ≤ (229528482172592539/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683470325879/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0616_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009723826831/500000000000 : ℝ) ≤ 4*Real.exp (81/512 : ℝ)*Real.exp (-mu (radius 7 (163/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (1009723826831/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (163/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0616_exp_radius
  have hrNumeric : (244379162173/250000000000 : ℝ) ≤ Real.exp (-163/7168 : ℝ) ∧ Real.exp (-163/7168 : ℝ) ≤ (977516648693/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (244379162173/250000000000 : ℝ) ≤ (radius 7 (163/1024 : ℝ)) ∧ (radius 7 (163/1024 : ℝ)) ≤ (977516648693/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (163/1024 : ℝ)) (244379162173/250000000000 : ℝ) (977516648693/1000000000000 : ℝ) (42171649969/200000000000 : ℝ) (210858249851/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (163/1024 : ℝ)) (244379162173/250000000000 : ℝ) (977516648693/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (163/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (244379162173/250000000000 : ℝ) (977516648693/1000000000000 : ℝ) (494379162173/500000000000 : ℝ) (988758324347/1000000000000 : ℝ) (988694416233/1000000000000 : ℝ) (197738883247/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (163/1024 : ℝ)) 1 (494379162173/500000000000 : ℝ) (988758324347/1000000000000 : ℝ) (988694416233/1000000000000 : ℝ) (197738883247/200000000000 : ℝ) (988726370289/1000000000000 : ℝ) (988726370291/1000000000000 : ℝ) (988726369773/1000000000000 : ℝ) (39549054791/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (163/1024 : ℝ)) 2 (988726370289/1000000000000 : ℝ) (988726370291/1000000000000 : ℝ) (988726369773/1000000000000 : ℝ) (39549054791/40000000000 : ℝ) (988726370031/1000000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (163/1024 : ℝ)) 3 (988726370031/1000000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (163/1024 : ℝ)) 4 (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (163/1024 : ℝ)) 5 (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (163/1024 : ℝ)) 6 (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (163/1024 : ℝ)) 7 (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (163/1024 : ℝ))) (42171649969/200000000000 : ℝ) (210858249851/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (163/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (42171649969/200000000000 : ℝ) (210858249851/1000000000000 : ℝ) (302714562461/500000000000 : ℝ) (302714562463/500000000000 : ℝ) (18367721681/40000000000 : ℝ) (459193042033/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (163/1024 : ℝ))) 1 (302714562461/500000000000 : ℝ) (302714562463/500000000000 : ℝ) (18367721681/40000000000 : ℝ) (459193042033/1000000000000 : ℝ) (532311083473/1000000000000 : ℝ) (13307777087/25000000000 : ℝ) (6590817969/12500000000 : ℝ) (527265437527/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (163/1024 : ℝ))) 2 (532311083473/1000000000000 : ℝ) (13307777087/25000000000 : ℝ) (6590817969/12500000000 : ℝ) (527265437527/1000000000000 : ℝ) (33111766281/62500000000 : ℝ) (66223532563/125000000000 : ℝ) (529782253689/1000000000000 : ℝ) (529782253697/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (163/1024 : ℝ))) 3 (33111766281/62500000000 : ℝ) (66223532563/125000000000 : ℝ) (529782253689/1000000000000 : ℝ) (529782253697/1000000000000 : ℝ) (132446314273/250000000000 : ℝ) (529785257101/1000000000000 : ℝ) (529785257083/1000000000000 : ℝ) (132446314273/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (163/1024 : ℝ))) 4 (132446314273/250000000000 : ℝ) (529785257101/1000000000000 : ℝ) (529785257083/1000000000000 : ℝ) (132446314273/250000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (163/1024 : ℝ))) 5 (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (163/1024 : ℝ))) 6 (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (163/1024 : ℝ))) 7 (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (163/1024 : ℝ)) hmem 8 (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (163/1024 : ℝ))) hcmem 8 (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (163/1024 : ℝ)) (98872637003/100000000000 : ℝ) (988726370033/1000000000000 : ℝ) (529785257087/1000000000000 : ℝ) (529785257097/1000000000000 : ℝ) (42083672543/50000000000 : ℝ) (841673450879/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0616_exp_lower
  have heNumeric : (1009723826831/500000000000 : ℝ)/4 ≤ Real.exp (-683470325879/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009723826831/500000000000 : ℝ)/4 ≤ Real.exp ((81/512 : ℝ)-(841673450879/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (81/512 : ℝ) (163/1024 : ℝ) (841673450879/1000000000000 : ℝ) (1009723826831/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0617; no trusted numerical premise.
theorem cover7_leaf0617_exp_radius : (199428830535377437/200000000000000000 : ℝ) ≤ Real.exp ((-41/1792 : ℝ)/8) ∧ Real.exp ((-41/1792 : ℝ)/8) ≤ (498572076338443593/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-41/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0617_exp_lower : (918125135645055627/1000000000000000000 : ℝ) ≤ Real.exp ((-683372674501/1000000000000 : ℝ)/8) ∧ Real.exp ((-683372674501/1000000000000 : ℝ)/8) ≤ (229531283911263907/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683372674501/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0617_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019644865137/1000000000000 : ℝ) ≤ 4*Real.exp (163/1024 : ℝ)*Real.exp (-mu (radius 7 (41/256 : ℝ))) ∧ (2019/1000 : ℝ) < (2019644865137/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (41/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0617_exp_radius
  have hrNumeric : (61086267869/62500000000 : ℝ) ≤ Real.exp (-41/1792 : ℝ) ∧ Real.exp (-41/1792 : ℝ) ≤ (195476057181/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61086267869/62500000000 : ℝ) ≤ (radius 7 (41/256 : ℝ)) ∧ (radius 7 (41/256 : ℝ)) ≤ (195476057181/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (41/256 : ℝ)) (61086267869/62500000000 : ℝ) (195476057181/200000000000 : ℝ) (42297884923/200000000000 : ℝ) (211489424621/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (41/256 : ℝ)) (61086267869/62500000000 : ℝ) (195476057181/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (41/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61086267869/62500000000 : ℝ) (195476057181/200000000000 : ℝ) (123586267869/125000000000 : ℝ) (988690142953/1000000000000 : ℝ) (988625452789/1000000000000 : ℝ) (988625452791/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (41/256 : ℝ)) 1 (123586267869/125000000000 : ℝ) (988690142953/1000000000000 : ℝ) (988625452789/1000000000000 : ℝ) (988625452791/1000000000000 : ℝ) (98865779787/100000000000 : ℝ) (61791112367/62500000000 : ℝ) (988657797341/1000000000000 : ℝ) (988657797343/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (41/256 : ℝ)) 2 (98865779787/100000000000 : ℝ) (61791112367/62500000000 : ℝ) (988657797341/1000000000000 : ℝ) (988657797343/1000000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (41/256 : ℝ)) 3 (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (41/256 : ℝ)) 4 (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (41/256 : ℝ)) 5 (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (41/256 : ℝ)) 6 (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (41/256 : ℝ)) 7 (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (41/256 : ℝ))) (42297884923/200000000000 : ℝ) (211489424621/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (41/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (42297884923/200000000000 : ℝ) (211489424621/1000000000000 : ℝ) (605744712307/1000000000000 : ℝ) (605744712311/1000000000000 : ℝ) (229939896829/500000000000 : ℝ) (91975958733/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (41/256 : ℝ))) 1 (605744712307/1000000000000 : ℝ) (605744712311/1000000000000 : ℝ) (229939896829/500000000000 : ℝ) (91975958733/200000000000 : ℝ) (266406126491/500000000000 : ℝ) (133203063247/250000000000 : ℝ) (527797075877/1000000000000 : ℝ) (131949268971/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (41/256 : ℝ))) 2 (266406126491/500000000000 : ℝ) (133203063247/250000000000 : ℝ) (527797075877/1000000000000 : ℝ) (131949268971/250000000000 : ℝ) (530304664429/1000000000000 : ℝ) (132576166109/250000000000 : ℝ) (33143670983/62500000000 : ℝ) (66287341967/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (41/256 : ℝ))) 3 (530304664429/1000000000000 : ℝ) (132576166109/250000000000 : ℝ) (33143670983/62500000000 : ℝ) (66287341967/125000000000 : ℝ) (265150850039/500000000000 : ℝ) (265150850043/500000000000 : ℝ) (53030170007/100000000000 : ℝ) (265150850039/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (41/256 : ℝ))) 4 (265150850039/500000000000 : ℝ) (265150850043/500000000000 : ℝ) (53030170007/100000000000 : ℝ) (265150850039/500000000000 : ℝ) (265150850037/500000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (41/256 : ℝ))) 5 (265150850037/500000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (41/256 : ℝ))) 6 (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (41/256 : ℝ))) 7 (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (41/256 : ℝ)) hmem 8 (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (41/256 : ℝ))) hcmem 8 (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (41/256 : ℝ)) (197731559521/200000000000 : ℝ) (123582224701/125000000000 : ℝ) (530301700073/1000000000000 : ℝ) (265150850041/500000000000 : ℝ) (842552361983/1000000000000 : ℝ) (842552362001/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0617_exp_lower
  have heNumeric : (2019644865137/1000000000000 : ℝ)/4 ≤ Real.exp (-683372674501/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019644865137/1000000000000 : ℝ)/4 ≤ Real.exp ((163/1024 : ℝ)-(842552362001/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (163/1024 : ℝ) (41/256 : ℝ) (842552362001/1000000000000 : ℝ) (2019644865137/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0618; no trusted numerical premise.
theorem cover7_leaf0618_exp_radius : (124640845501807291/125000000000000000 : ℝ) ≤ Real.exp ((-165/7168 : ℝ)/8) ∧ Real.exp ((-165/7168 : ℝ)/8) ≤ (997126764014458329/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-165/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0618_exp_lower : (918136746993092363/1000000000000000000 : ℝ) ≤ Real.exp ((-341635750357/500000000000 : ℝ)/8) ∧ Real.exp ((-341635750357/500000000000 : ℝ)/8) ≤ (229534186748273091/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341635750357/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0618_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019849210593/1000000000000 : ℝ) ≤ 4*Real.exp (41/256 : ℝ)*Real.exp (-mu (radius 7 (165/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2019849210593/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (165/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0618_exp_radius
  have hrNumeric : (488621971069/500000000000 : ℝ) ≤ Real.exp (-165/7168 : ℝ) ∧ Real.exp (-165/7168 : ℝ) ≤ (977243942139/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (488621971069/500000000000 : ℝ) ≤ (radius 7 (165/1024 : ℝ)) ∧ (radius 7 (165/1024 : ℝ)) ≤ (977243942139/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (165/1024 : ℝ)) (488621971069/500000000000 : ℝ) (977243942139/1000000000000 : ℝ) (212118545989/1000000000000 : ℝ) (106059272997/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (165/1024 : ℝ)) (488621971069/500000000000 : ℝ) (977243942139/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (165/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (488621971069/500000000000 : ℝ) (977243942139/1000000000000 : ℝ) (988621971069/1000000000000 : ℝ) (98862197107/100000000000 : ℝ) (197711298831/200000000000 : ℝ) (988556494157/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (165/1024 : ℝ)) 1 (988621971069/1000000000000 : ℝ) (98862197107/100000000000 : ℝ) (197711298831/200000000000 : ℝ) (988556494157/1000000000000 : ℝ) (247147308153/250000000000 : ℝ) (494294616307/500000000000 : ℝ) (988589232069/1000000000000 : ℝ) (123573654009/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (165/1024 : ℝ)) 2 (247147308153/250000000000 : ℝ) (494294616307/500000000000 : ℝ) (988589232069/1000000000000 : ℝ) (123573654009/125000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (165/1024 : ℝ)) 3 (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (165/1024 : ℝ)) 4 (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (165/1024 : ℝ)) 5 (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (165/1024 : ℝ)) 6 (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (165/1024 : ℝ)) 7 (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (165/1024 : ℝ))) (212118545989/1000000000000 : ℝ) (106059272997/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (165/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (212118545989/1000000000000 : ℝ) (106059272997/500000000000 : ℝ) (303029636497/500000000000 : ℝ) (606059272997/1000000000000 : ℝ) (92112658411/200000000000 : ℝ) (460563292061/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (165/1024 : ℝ))) 1 (303029636497/500000000000 : ℝ) (606059272997/1000000000000 : ℝ) (92112658411/200000000000 : ℝ) (460563292061/1000000000000 : ℝ) (133327820631/250000000000 : ℝ) (533311282529/1000000000000 : ℝ) (132081569009/250000000000 : ℝ) (264163138021/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (165/1024 : ℝ))) 2 (133327820631/250000000000 : ℝ) (533311282529/1000000000000 : ℝ) (132081569009/250000000000 : ℝ) (264163138021/500000000000 : ℝ) (6635234741/12500000000 : ℝ) (265409389643/500000000000 : ℝ) (53081292737/100000000000 : ℝ) (530812927377/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (165/1024 : ℝ))) 3 (6635234741/12500000000 : ℝ) (265409389643/500000000000 : ℝ) (53081292737/100000000000 : ℝ) (530812927377/1000000000000 : ℝ) (21232634133/40000000000 : ℝ) (132703963333/250000000000 : ℝ) (132703963329/250000000000 : ℝ) (132703963331/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (165/1024 : ℝ))) 4 (21232634133/40000000000 : ℝ) (132703963333/250000000000 : ℝ) (132703963329/250000000000 : ℝ) (132703963331/250000000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (165/1024 : ℝ))) 5 (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (165/1024 : ℝ))) 6 (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (165/1024 : ℝ))) 7 (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (165/1024 : ℝ)) hmem 8 (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (165/1024 : ℝ))) hcmem 8 (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (165/1024 : ℝ)) (49429461617/50000000000 : ℝ) (988589232343/1000000000000 : ℝ) (13270396333/25000000000 : ℝ) (33175990833/62500000000 : ℝ) (421713875349/500000000000 : ℝ) (421713875357/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0618_exp_lower
  have heNumeric : (2019849210593/1000000000000 : ℝ)/4 ≤ Real.exp (-341635750357/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019849210593/1000000000000 : ℝ)/4 ≤ Real.exp ((41/256 : ℝ)-(421713875357/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (41/256 : ℝ) (165/1024 : ℝ) (421713875357/500000000000 : ℝ) (2019849210593/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0619; no trusted numerical premise.
theorem cover7_leaf0619_exp_radius : (199421875131052207/200000000000000000 : ℝ) ≤ Real.exp ((-83/3584 : ℝ)/8) ∧ Real.exp ((-83/3584 : ℝ)/8) ≤ (249277343913815259/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0619_exp_lower : (28692148702495441/31250000000000000 : ℝ) ≤ Real.exp ((-683166841723/1000000000000 : ℝ)/8) ∧ Real.exp ((-683166841723/1000000000000 : ℝ)/8) ≤ (918148758479854113/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683166841723/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0619_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505015154259/250000000000 : ℝ) ≤ 4*Real.exp (165/1024 : ℝ)*Real.exp (-mu (radius 7 (83/512 : ℝ))) ∧ (2019/1000 : ℝ) < (505015154259/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (83/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0619_exp_radius
  have hrNumeric : (61069226087/62500000000 : ℝ) ≤ Real.exp (-83/3584 : ℝ) ∧ Real.exp (-83/3584 : ℝ) ≤ (977107617393/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61069226087/62500000000 : ℝ) ≤ (radius 7 (83/512 : ℝ)) ∧ (radius 7 (83/512 : ℝ)) ≤ (977107617393/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (83/512 : ℝ)) (61069226087/62500000000 : ℝ) (977107617393/1000000000000 : ℝ) (212745632229/1000000000000 : ℝ) (106372816117/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (83/512 : ℝ)) (61069226087/62500000000 : ℝ) (977107617393/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (83/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61069226087/62500000000 : ℝ) (977107617393/1000000000000 : ℝ) (123569226087/125000000000 : ℝ) (988553808697/1000000000000 : ℝ) (247121885083/250000000000 : ℝ) (988487540333/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (83/512 : ℝ)) 1 (123569226087/125000000000 : ℝ) (988553808697/1000000000000 : ℝ) (247121885083/250000000000 : ℝ) (988487540333/1000000000000 : ℝ) (494260337257/500000000000 : ℝ) (197704134903/200000000000 : ℝ) (494260336979/500000000000 : ℝ) (24713016849/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (83/512 : ℝ)) 2 (494260337257/500000000000 : ℝ) (197704134903/200000000000 : ℝ) (494260336979/500000000000 : ℝ) (24713016849/25000000000 : ℝ) (247130168559/250000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (83/512 : ℝ)) 3 (247130168559/250000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (83/512 : ℝ)) 4 (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (83/512 : ℝ)) 5 (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (83/512 : ℝ)) 6 (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (83/512 : ℝ)) 7 (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (83/512 : ℝ))) (212745632229/1000000000000 : ℝ) (106372816117/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (83/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (212745632229/1000000000000 : ℝ) (106372816117/500000000000 : ℝ) (303186408057/500000000000 : ℝ) (606372816117/1000000000000 : ℝ) (461243571477/1000000000000 : ℝ) (461243571483/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (83/512 : ℝ))) 1 (303186408057/500000000000 : ℝ) (606372816117/1000000000000 : ℝ) (461243571477/1000000000000 : ℝ) (461243571483/1000000000000 : ℝ) (106761638759/200000000000 : ℝ) (2669040969/5000000000 : ℝ) (264426532023/500000000000 : ℝ) (528853064051/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (83/512 : ℝ))) 2 (106761638759/200000000000 : ℝ) (2669040969/5000000000 : ℝ) (264426532023/500000000000 : ℝ) (528853064051/1000000000000 : ℝ) (13283265723/25000000000 : ℝ) (265665314463/500000000000 : ℝ) (132831213129/250000000000 : ℝ) (265662426261/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (83/512 : ℝ))) 3 (13283265723/25000000000 : ℝ) (265665314463/500000000000 : ℝ) (132831213129/250000000000 : ℝ) (265662426261/500000000000 : ℝ) (265663870359/500000000000 : ℝ) (132831935181/250000000000 : ℝ) (53132774071/100000000000 : ℝ) (531327740717/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (83/512 : ℝ))) 4 (265663870359/500000000000 : ℝ) (132831935181/250000000000 : ℝ) (53132774071/100000000000 : ℝ) (531327740717/1000000000000 : ℝ) (265663870357/500000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (83/512 : ℝ))) 5 (265663870357/500000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (83/512 : ℝ))) 6 (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (83/512 : ℝ))) 7 (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (83/512 : ℝ)) hmem 8 (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (83/512 : ℝ))) hcmem 8 (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (83/512 : ℝ)) (197704134847/200000000000 : ℝ) (494260337119/500000000000 : ℝ) (531327740713/1000000000000 : ℝ) (531327740721/1000000000000 : ℝ) (844299654207/1000000000000 : ℝ) (844299654223/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0619_exp_lower
  have heNumeric : (505015154259/250000000000 : ℝ)/4 ≤ Real.exp (-683166841723/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505015154259/250000000000 : ℝ)/4 ≤ Real.exp ((165/1024 : ℝ)-(844299654223/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (165/1024 : ℝ) (83/512 : ℝ) (844299654223/1000000000000 : ℝ) (505015154259/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0620; no trusted numerical premise.
theorem cover7_leaf0620_exp_radius : (498545993799645009/500000000000000000 : ℝ) ≤ Real.exp ((-167/7168 : ℝ)/8) ∧ Real.exp ((-167/7168 : ℝ)/8) ≤ (997091987599290019/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-167/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0620_exp_lower : (459080582961030401/500000000000000000 : ℝ) ≤ Real.exp ((-341529367057/500000000000 : ℝ)/8) ∧ Real.exp ((-341529367057/500000000000 : ℝ)/8) ≤ (918161165922060803/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341529367057/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0620_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (505069753191/250000000000 : ℝ) ≤ 4*Real.exp (83/512 : ℝ)*Real.exp (-mu (radius 7 (167/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (505069753191/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (167/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0620_exp_radius
  have hrNumeric : (61060706979/62500000000 : ℝ) ≤ Real.exp (-167/7168 : ℝ) ∧ Real.exp (-167/7168 : ℝ) ≤ (195394262333/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61060706979/62500000000 : ℝ) ≤ (radius 7 (167/1024 : ℝ)) ∧ (radius 7 (167/1024 : ℝ)) ≤ (195394262333/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (167/1024 : ℝ)) (61060706979/62500000000 : ℝ) (195394262333/200000000000 : ℝ) (53342675331/250000000000 : ℝ) (213370701329/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (167/1024 : ℝ)) (61060706979/62500000000 : ℝ) (195394262333/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (167/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61060706979/62500000000 : ℝ) (195394262333/200000000000 : ℝ) (123560706979/125000000000 : ℝ) (988485655833/1000000000000 : ℝ) (494209295659/500000000000 : ℝ) (988418591319/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (167/1024 : ℝ)) 1 (123560706979/125000000000 : ℝ) (988485655833/1000000000000 : ℝ) (494209295659/500000000000 : ℝ) (988418591319/1000000000000 : ℝ) (39538084943/40000000000 : ℝ) (123556515447/125000000000 : ℝ) (494226061503/500000000000 : ℝ) (7722282211/7812500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (167/1024 : ℝ)) 2 (39538084943/40000000000 : ℝ) (123556515447/125000000000 : ℝ) (494226061503/500000000000 : ℝ) (7722282211/7812500000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (167/1024 : ℝ)) 3 (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (167/1024 : ℝ)) 4 (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (167/1024 : ℝ)) 5 (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (167/1024 : ℝ)) 6 (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (167/1024 : ℝ)) 7 (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (167/1024 : ℝ))) (53342675331/250000000000 : ℝ) (213370701329/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (167/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (53342675331/250000000000 : ℝ) (213370701329/1000000000000 : ℝ) (303342675331/500000000000 : ℝ) (121337070133/200000000000 : ℝ) (28870041601/62500000000 : ℝ) (461920665623/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (167/1024 : ℝ))) 1 (303342675331/500000000000 : ℝ) (121337070133/200000000000 : ℝ) (28870041601/62500000000 : ℝ) (461920665623/1000000000000 : ℝ) (534303008139/1000000000000 : ℝ) (33393938009/62500000000 : ℝ) (529377465517/1000000000000 : ℝ) (529377465523/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (167/1024 : ℝ))) 2 (534303008139/1000000000000 : ℝ) (33393938009/62500000000 : ℝ) (529377465517/1000000000000 : ℝ) (529377465523/1000000000000 : ℝ) (132960059207/250000000000 : ℝ) (265920118417/500000000000 : ℝ) (531834534669/1000000000000 : ℝ) (21273381387/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (167/1024 : ℝ))) 3 (132960059207/250000000000 : ℝ) (265920118417/500000000000 : ℝ) (531834534669/1000000000000 : ℝ) (21273381387/40000000000 : ℝ) (132959346437/250000000000 : ℝ) (106367477151/200000000000 : ℝ) (26591869287/50000000000 : ℝ) (531837385747/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (167/1024 : ℝ))) 4 (132959346437/250000000000 : ℝ) (106367477151/200000000000 : ℝ) (26591869287/50000000000 : ℝ) (531837385747/1000000000000 : ℝ) (33239836609/62500000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (167/1024 : ℝ))) 5 (33239836609/62500000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (167/1024 : ℝ))) 6 (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (167/1024 : ℝ))) 7 (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (167/1024 : ℝ)) hmem 8 (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (167/1024 : ℝ))) hcmem 8 (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (167/1024 : ℝ)) (98845212329/100000000000 : ℝ) (247113030823/250000000000 : ℝ) (531837385743/1000000000000 : ℝ) (531837385751/1000000000000 : ℝ) (422584054549/500000000000 : ℝ) (422584054557/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0620_exp_lower
  have heNumeric : (505069753191/250000000000 : ℝ)/4 ≤ Real.exp (-341529367057/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (505069753191/250000000000 : ℝ)/4 ≤ Real.exp ((83/512 : ℝ)-(422584054557/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (83/512 : ℝ) (167/1024 : ℝ) (422584054557/500000000000 : ℝ) (505069753191/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0621; no trusted numerical premise.
theorem cover7_leaf0621_exp_radius : (997074599846539989/1000000000000000000 : ℝ) ≤ Real.exp ((-3/128 : ℝ)/8) ∧ Real.exp ((-3/128 : ℝ)/8) ≤ (99707459984653999/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/128 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0621_exp_lower : (229543491301051773/250000000000000000 : ℝ) ≤ Real.exp ((-136589442777/200000000000 : ℝ)/8) ∧ Real.exp ((-136589442777/200000000000 : ℝ)/8) ≤ (918173965204207093/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-136589442777/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0621_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1010252163653/500000000000 : ℝ) ≤ 4*Real.exp (167/1024 : ℝ)*Real.exp (-mu (radius 7 (21/128 : ℝ))) ∧ (2019/1000 : ℝ) < (1010252163653/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (21/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0621_exp_radius
  have hrNumeric : (19536700499/20000000000 : ℝ) ≤ Real.exp (-3/128 : ℝ) ∧ Real.exp (-3/128 : ℝ) ≤ (976835024951/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19536700499/20000000000 : ℝ) ≤ (radius 7 (21/128 : ℝ)) ∧ (radius 7 (21/128 : ℝ)) ≤ (976835024951/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (21/128 : ℝ)) (19536700499/20000000000 : ℝ) (976835024951/1000000000000 : ℝ) (42798754201/200000000000 : ℝ) (21399377101/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (21/128 : ℝ)) (19536700499/20000000000 : ℝ) (976835024951/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (21/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19536700499/20000000000 : ℝ) (976835024951/1000000000000 : ℝ) (39536700499/40000000000 : ℝ) (247104378119/250000000000 : ℝ) (988349647113/1000000000000 : ℝ) (197669929423/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (21/128 : ℝ)) 1 (39536700499/40000000000 : ℝ) (247104378119/250000000000 : ℝ) (988349647113/1000000000000 : ℝ) (197669929423/200000000000 : ℝ) (494191789897/500000000000 : ℝ) (247095894949/250000000000 : ℝ) (988383579211/1000000000000 : ℝ) (494191789607/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (21/128 : ℝ)) 2 (494191789897/500000000000 : ℝ) (247095894949/250000000000 : ℝ) (988383579211/1000000000000 : ℝ) (494191789607/500000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (21/128 : ℝ)) 3 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (21/128 : ℝ)) 4 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (21/128 : ℝ)) 5 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (21/128 : ℝ)) 6 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (21/128 : ℝ)) 7 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (21/128 : ℝ))) (42798754201/200000000000 : ℝ) (21399377101/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (21/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (42798754201/200000000000 : ℝ) (21399377101/100000000000 : ℝ) (303498442751/500000000000 : ℝ) (121399377101/200000000000 : ℝ) (231297303813/500000000000 : ℝ) (28912162977/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (21/128 : ℝ))) 1 (303498442751/500000000000 : ℝ) (121399377101/200000000000 : ℝ) (231297303813/500000000000 : ℝ) (28912162977/62500000000 : ℝ) (133698936641/250000000000 : ℝ) (534795746569/1000000000000 : ℝ) (529899505641/1000000000000 : ℝ) (529899505647/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (21/128 : ℝ))) 2 (133698936641/250000000000 : ℝ) (534795746569/1000000000000 : ℝ) (529899505641/1000000000000 : ℝ) (529899505647/1000000000000 : ℝ) (266173813051/500000000000 : ℝ) (133086906527/250000000000 : ℝ) (133085499239/250000000000 : ℝ) (266170998481/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (21/128 : ℝ))) 3 (266173813051/500000000000 : ℝ) (133086906527/250000000000 : ℝ) (133085499239/250000000000 : ℝ) (266170998481/500000000000 : ℝ) (532344811529/1000000000000 : ℝ) (106468962307/200000000000 : ℝ) (532344811521/1000000000000 : ℝ) (66543101441/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (21/128 : ℝ))) 4 (532344811529/1000000000000 : ℝ) (106468962307/200000000000 : ℝ) (532344811521/1000000000000 : ℝ) (66543101441/125000000000 : ℝ) (21293792461/40000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (21/128 : ℝ))) 5 (21293792461/40000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (21/128 : ℝ))) 6 (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (21/128 : ℝ))) 7 (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (21/128 : ℝ)) hmem 8 (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (21/128 : ℝ))) hcmem 8 (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (21/128 : ℝ)) (494191789751/500000000000 : ℝ) (197676715901/200000000000 : ℝ) (133086202881/250000000000 : ℝ) (133086202883/250000000000 : ℝ) (846033151369/1000000000000 : ℝ) (169206630277/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0621_exp_lower
  have heNumeric : (1010252163653/500000000000 : ℝ)/4 ≤ Real.exp (-136589442777/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1010252163653/500000000000 : ℝ)/4 ≤ Real.exp ((167/1024 : ℝ)-(169206630277/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (167/1024 : ℝ) (21/128 : ℝ) (169206630277/200000000000 : ℝ) (1010252163653/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0622; no trusted numerical premise.
theorem cover7_leaf0622_exp_radius : (498519912625340873/500000000000000000 : ℝ) ≤ Real.exp ((-85/3584 : ℝ)/8) ∧ Real.exp ((-85/3584 : ℝ)/8) ≤ (997039825250681747/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0622_exp_lower : (918088644961089141/1000000000000000000 : ℝ) ≤ Real.exp ((-683690639081/1000000000000 : ℝ)/8) ∧ Real.exp ((-683690639081/1000000000000 : ℝ)/8) ≤ (459044322480544571/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683690639081/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0622_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019002791689/1000000000000 : ℝ) ≤ 4*Real.exp (21/128 : ℝ)*Real.exp (-mu (radius 7 (85/512 : ℝ))) ∧ (2019/1000 : ℝ) < (2019002791689/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (85/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0622_exp_radius
  have hrNumeric : (488281254277/500000000000 : ℝ) ≤ Real.exp (-85/3584 : ℝ) ∧ Real.exp (-85/3584 : ℝ) ≤ (195312501711/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (488281254277/500000000000 : ℝ) ≤ (radius 7 (85/512 : ℝ)) ∧ (radius 7 (85/512 : ℝ)) ≤ (195312501711/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (85/512 : ℝ)) (488281254277/500000000000 : ℝ) (195312501711/200000000000 : ℝ) (107616990857/500000000000 : ℝ) (5380849543/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (85/512 : ℝ)) (488281254277/500000000000 : ℝ) (195312501711/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (85/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (488281254277/500000000000 : ℝ) (195312501711/200000000000 : ℝ) (988281254277/1000000000000 : ℝ) (494140627139/500000000000 : ℝ) (98821177313/100000000000 : ℝ) (247052943283/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (85/512 : ℝ)) 1 (988281254277/1000000000000 : ℝ) (494140627139/500000000000 : ℝ) (98821177313/100000000000 : ℝ) (247052943283/250000000000 : ℝ) (988246513703/1000000000000 : ℝ) (197649302741/200000000000 : ℝ) (247061628273/250000000000 : ℝ) (197649302619/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (85/512 : ℝ)) 2 (988246513703/1000000000000 : ℝ) (197649302741/200000000000 : ℝ) (247061628273/250000000000 : ℝ) (197649302619/200000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (85/512 : ℝ)) 3 (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (85/512 : ℝ)) 4 (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (85/512 : ℝ)) 5 (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (85/512 : ℝ)) 6 (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (85/512 : ℝ)) 7 (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (85/512 : ℝ))) (107616990857/500000000000 : ℝ) (5380849543/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (85/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (107616990857/500000000000 : ℝ) (5380849543/25000000000 : ℝ) (607616990857/1000000000000 : ℝ) (30380849543/50000000000 : ℝ) (28995822821/62500000000 : ℝ) (57991645643/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (85/512 : ℝ))) 1 (607616990857/1000000000000 : ℝ) (30380849543/50000000000 : ℝ) (28995822821/62500000000 : ℝ) (57991645643/125000000000 : ℝ) (133943769499/250000000000 : ℝ) (267887539001/500000000000 : ℝ) (530936600507/1000000000000 : ℝ) (265468300257/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (85/512 : ℝ))) 2 (133943769499/250000000000 : ℝ) (267887539001/500000000000 : ℝ) (530936600507/1000000000000 : ℝ) (265468300257/500000000000 : ℝ) (533355839251/1000000000000 : ℝ) (266677919629/500000000000 : ℝ) (533350352533/1000000000000 : ℝ) (26667517627/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (85/512 : ℝ))) 3 (533355839251/1000000000000 : ℝ) (266677919629/500000000000 : ℝ) (533350352533/1000000000000 : ℝ) (26667517627/50000000000 : ℝ) (133338273973/250000000000 : ℝ) (533353095899/1000000000000 : ℝ) (133338273971/250000000000 : ℝ) (133338273973/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (85/512 : ℝ))) 4 (133338273973/250000000000 : ℝ) (533353095899/1000000000000 : ℝ) (133338273971/250000000000 : ℝ) (133338273973/250000000000 : ℝ) (33334568493/62500000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (85/512 : ℝ))) 5 (33334568493/62500000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (85/512 : ℝ))) 6 (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (85/512 : ℝ))) 7 (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (85/512 : ℝ)) hmem 8 (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (85/512 : ℝ))) hcmem 8 (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (85/512 : ℝ)) (988246513397/1000000000000 : ℝ) (4941232567/5000000000 : ℝ) (533353095887/1000000000000 : ℝ) (66669136987/125000000000 : ℝ) (105969142383/125000000000 : ℝ) (847753139081/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0622_exp_lower
  have heNumeric : (2019002791689/1000000000000 : ℝ)/4 ≤ Real.exp (-683690639081/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019002791689/1000000000000 : ℝ)/4 ≤ Real.exp ((21/128 : ℝ)-(847753139081/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (21/128 : ℝ) (85/512 : ℝ) (847753139081/1000000000000 : ℝ) (2019002791689/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0623; no trusted numerical premise.
theorem cover7_leaf0623_exp_radius : (199401010373528801/200000000000000000 : ℝ) ≤ Real.exp ((-43/1792 : ℝ)/8) ∧ Real.exp ((-43/1792 : ℝ)/8) ≤ (498502525933822003/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-43/1792 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0623_exp_lower : (183623383826670263/200000000000000000 : ℝ) ≤ Real.exp ((-13668885373/20000000000 : ℝ)/8) ∧ Real.exp ((-13668885373/20000000000 : ℝ)/8) ≤ (229529229783337829/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-13668885373/20000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0623_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019500275557/1000000000000 : ℝ) ≤ 4*Real.exp (85/512 : ℝ)*Real.exp (-mu (radius 7 (43/256 : ℝ))) ∧ (2019/1000 : ℝ) < (2019500275557/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (43/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0623_exp_radius
  have hrNumeric : (195258013637/200000000000 : ℝ) ≤ Real.exp (-43/1792 : ℝ) ∧ Real.exp (-43/1792 : ℝ) ≤ (488145034093/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (195258013637/200000000000 : ℝ) ≤ (radius 7 (43/256 : ℝ)) ∧ (radius 7 (43/256 : ℝ)) ≤ (488145034093/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (43/256 : ℝ)) (195258013637/200000000000 : ℝ) (488145034093/500000000000 : ℝ) (108233200499/500000000000 : ℝ) (54116600251/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (43/256 : ℝ)) (195258013637/200000000000 : ℝ) (488145034093/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (43/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (195258013637/200000000000 : ℝ) (488145034093/500000000000 : ℝ) (247036258523/250000000000 : ℝ) (988145034093/1000000000000 : ℝ) (988073918381/1000000000000 : ℝ) (494036959191/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (43/256 : ℝ)) 1 (247036258523/250000000000 : ℝ) (988145034093/1000000000000 : ℝ) (988073918381/1000000000000 : ℝ) (494036959191/500000000000 : ℝ) (247027369059/250000000000 : ℝ) (494054738119/500000000000 : ℝ) (247027368899/250000000000 : ℝ) (494054737799/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (43/256 : ℝ)) 2 (247027369059/250000000000 : ℝ) (494054738119/500000000000 : ℝ) (247027368899/250000000000 : ℝ) (494054737799/500000000000 : ℝ) (247027368979/250000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (43/256 : ℝ)) 3 (247027368979/250000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (43/256 : ℝ)) 4 (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (43/256 : ℝ)) 5 (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (43/256 : ℝ)) 6 (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (43/256 : ℝ)) 7 (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (43/256 : ℝ))) (108233200499/500000000000 : ℝ) (54116600251/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (43/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (108233200499/500000000000 : ℝ) (54116600251/250000000000 : ℝ) (608233200499/1000000000000 : ℝ) (304116600251/500000000000 : ℝ) (465259498557/1000000000000 : ℝ) (116314874641/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (43/256 : ℝ))) 1 (608233200499/1000000000000 : ℝ) (304116600251/500000000000 : ℝ) (465259498557/1000000000000 : ℝ) (116314874641/250000000000 : ℝ) (67093293691/125000000000 : ℝ) (536746349533/1000000000000 : ℝ) (531964541929/1000000000000 : ℝ) (106392908387/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (43/256 : ℝ))) 2 (67093293691/125000000000 : ℝ) (536746349533/1000000000000 : ℝ) (531964541929/1000000000000 : ℝ) (106392908387/200000000000 : ℝ) (16698607679/31250000000 : ℝ) (267177722867/500000000000 : ℝ) (66793762101/125000000000 : ℝ) (267175048407/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (43/256 : ℝ))) 3 (16698607679/31250000000 : ℝ) (267177722867/500000000000 : ℝ) (66793762101/125000000000 : ℝ) (267175048407/500000000000 : ℝ) (133588192817/250000000000 : ℝ) (267176385637/500000000000 : ℝ) (534352771261/1000000000000 : ℝ) (133588192817/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (43/256 : ℝ))) 4 (133588192817/250000000000 : ℝ) (267176385637/500000000000 : ℝ) (534352771261/1000000000000 : ℝ) (133588192817/250000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (43/256 : ℝ))) 5 (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (43/256 : ℝ))) 6 (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (43/256 : ℝ))) 7 (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (43/256 : ℝ)) hmem 8 (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (43/256 : ℝ))) hcmem 8 (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (43/256 : ℝ)) (197621895183/200000000000 : ℝ) (494054737959/500000000000 : ℝ) (8349262051/15625000000 : ℝ) (534352771271/1000000000000 : ℝ) (212364973409/250000000000 : ℝ) (16989197873/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0623_exp_lower
  have heNumeric : (2019500275557/1000000000000 : ℝ)/4 ≤ Real.exp (-13668885373/20000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019500275557/1000000000000 : ℝ)/4 ≤ Real.exp ((85/512 : ℝ)-(16989197873/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (85/512 : ℝ) (43/256 : ℝ) (16989197873/20000000000 : ℝ) (2019500275557/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0624; no trusted numerical premise.
theorem cover7_leaf0624_exp_radius : (249242569924346117/250000000000000000 : ℝ) ≤ Real.exp ((-87/3584 : ℝ)/8) ∧ Real.exp ((-87/3584 : ℝ)/8) ≤ (996970279697384469/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-87/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0624_exp_lower : (229536670553872233/250000000000000000 : ℝ) ≤ Real.exp ((-683184932619/1000000000000 : ℝ)/8) ∧ Real.exp ((-683184932619/1000000000000 : ℝ)/8) ≤ (918146682215488933/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683184932619/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0624_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (101001203633/50000000000 : ℝ) ≤ 4*Real.exp (43/256 : ℝ)*Real.exp (-mu (radius 7 (87/512 : ℝ))) ∧ (2019/1000 : ℝ) < (101001203633/50000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (87/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0624_exp_radius
  have hrNumeric : (488008851911/500000000000 : ℝ) ≤ Real.exp (-87/3584 : ℝ) ∧ Real.exp (-87/3584 : ℝ) ≤ (976017703823/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (488008851911/500000000000 : ℝ) ≤ (radius 7 (87/512 : ℝ)) ∧ (radius 7 (87/512 : ℝ)) ≤ (976017703823/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (87/512 : ℝ)) (488008851911/500000000000 : ℝ) (976017703823/1000000000000 : ℝ) (108845580783/500000000000 : ℝ) (217691161571/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (87/512 : ℝ)) (488008851911/500000000000 : ℝ) (976017703823/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (87/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (488008851911/500000000000 : ℝ) (976017703823/1000000000000 : ℝ) (988008851911/1000000000000 : ℝ) (123501106489/125000000000 : ℝ) (493968041431/500000000000 : ℝ) (61746005179/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (87/512 : ℝ)) 1 (988008851911/1000000000000 : ℝ) (123501106489/125000000000 : ℝ) (493968041431/500000000000 : ℝ) (61746005179/62500000000 : ℝ) (493986233693/500000000000 : ℝ) (246993116847/250000000000 : ℝ) (246993116679/250000000000 : ℝ) (987972466719/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (87/512 : ℝ)) 2 (493986233693/500000000000 : ℝ) (246993116847/250000000000 : ℝ) (246993116679/250000000000 : ℝ) (987972466719/1000000000000 : ℝ) (987972467051/1000000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (87/512 : ℝ)) 3 (987972467051/1000000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (87/512 : ℝ)) 4 (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (87/512 : ℝ)) 5 (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (87/512 : ℝ)) 6 (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (87/512 : ℝ)) 7 (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (87/512 : ℝ))) (108845580783/500000000000 : ℝ) (217691161571/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (87/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (108845580783/500000000000 : ℝ) (217691161571/1000000000000 : ℝ) (608845580783/1000000000000 : ℝ) (304422790393/500000000000 : ℝ) (466573854353/1000000000000 : ℝ) (466573854359/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (87/512 : ℝ))) 1 (608845580783/1000000000000 : ℝ) (304422790393/500000000000 : ℝ) (466573854353/1000000000000 : ℝ) (466573854359/1000000000000 : ℝ) (8401714337/15625000000 : ℝ) (537709717573/1000000000000 : ℝ) (532983516941/1000000000000 : ℝ) (532983516947/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (87/512 : ℝ))) 2 (8401714337/15625000000 : ℝ) (537709717573/1000000000000 : ℝ) (532983516941/1000000000000 : ℝ) (532983516947/1000000000000 : ℝ) (267673308627/500000000000 : ℝ) (26767330863/50000000000 : ℝ) (535341401689/1000000000000 : ℝ) (107068280339/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (87/512 : ℝ))) 3 (267673308627/500000000000 : ℝ) (26767330863/50000000000 : ℝ) (535341401689/1000000000000 : ℝ) (107068280339/200000000000 : ℝ) (535344009471/1000000000000 : ℝ) (267672004739/500000000000 : ℝ) (107068801893/200000000000 : ℝ) (2091187537/3906250000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (87/512 : ℝ))) 4 (535344009471/1000000000000 : ℝ) (267672004739/500000000000 : ℝ) (107068801893/200000000000 : ℝ) (2091187537/3906250000 : ℝ) (133836002367/250000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (87/512 : ℝ))) 5 (133836002367/250000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (87/512 : ℝ))) 6 (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (87/512 : ℝ))) 7 (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (87/512 : ℝ)) hmem 8 (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (87/512 : ℝ))) hcmem 8 (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (87/512 : ℝ)) (19759449341/20000000000 : ℝ) (493986233527/500000000000 : ℝ) (535344009467/1000000000000 : ℝ) (21413760379/40000000000 : ℝ) (425576841301/500000000000 : ℝ) (851153682619/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0624_exp_lower
  have heNumeric : (101001203633/50000000000 : ℝ)/4 ≤ Real.exp (-683184932619/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (101001203633/50000000000 : ℝ)/4 ≤ Real.exp ((43/256 : ℝ)-(851153682619/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (43/256 : ℝ) (87/512 : ℝ) (851153682619/1000000000000 : ℝ) (101001203633/50000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0600_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0600_certificate
#check SmaleRate.Proofs.cover7_leaf0601_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0601_certificate
#check SmaleRate.Proofs.cover7_leaf0602_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0602_certificate
#check SmaleRate.Proofs.cover7_leaf0603_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0603_certificate
#check SmaleRate.Proofs.cover7_leaf0604_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0604_certificate
#check SmaleRate.Proofs.cover7_leaf0605_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0605_certificate
#check SmaleRate.Proofs.cover7_leaf0606_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0606_certificate
#check SmaleRate.Proofs.cover7_leaf0607_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0607_certificate
#check SmaleRate.Proofs.cover7_leaf0608_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0608_certificate
#check SmaleRate.Proofs.cover7_leaf0609_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0609_certificate
#check SmaleRate.Proofs.cover7_leaf0610_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0610_certificate
#check SmaleRate.Proofs.cover7_leaf0611_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0611_certificate
#check SmaleRate.Proofs.cover7_leaf0612_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0612_certificate
#check SmaleRate.Proofs.cover7_leaf0613_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0613_certificate
#check SmaleRate.Proofs.cover7_leaf0614_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0614_certificate
#check SmaleRate.Proofs.cover7_leaf0615_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0615_certificate
#check SmaleRate.Proofs.cover7_leaf0616_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0616_certificate
#check SmaleRate.Proofs.cover7_leaf0617_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0617_certificate
#check SmaleRate.Proofs.cover7_leaf0618_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0618_certificate
#check SmaleRate.Proofs.cover7_leaf0619_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0619_certificate
#check SmaleRate.Proofs.cover7_leaf0620_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0620_certificate
#check SmaleRate.Proofs.cover7_leaf0621_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0621_certificate
#check SmaleRate.Proofs.cover7_leaf0622_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0622_certificate
#check SmaleRate.Proofs.cover7_leaf0623_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0623_certificate
#check SmaleRate.Proofs.cover7_leaf0624_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0624_certificate
