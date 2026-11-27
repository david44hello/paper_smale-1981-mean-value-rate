/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0950; no trusted numerical premise.
theorem cover8_leaf0950_exp_radius : (31187642265763481/31250000000000000 : ℝ) ≤ Real.exp ((-67023/4194304 : ℝ)/8) ∧ Real.exp ((-67023/4194304 : ℝ)/8) ≤ (998004552504431393/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67023/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0950_exp_lower : (184022691324646133/200000000000000000 : ℝ) ≤ Real.exp ((-42628246592553/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628246592553/64000000000000 : ℝ)/8) ≤ (460056728311615333/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628246592553/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0950_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450845743/500000000000 : ℝ) ≤ 4*Real.exp (33511/262144 : ℝ)*Real.exp (-mu (radius 8 (67023/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450845743/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67023/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0950_exp_radius
  have hrNumeric : (196829493379/200000000000 : ℝ) ≤ Real.exp (-67023/4194304 : ℝ) ∧ Real.exp (-67023/4194304 : ℝ) ≤ (61509216681/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196829493379/200000000000 : ℝ) ≤ (radius 8 (67023/524288 : ℝ)) ∧ (radius 8 (67023/524288 : ℝ)) ≤ (61509216681/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67023/524288 : ℝ)) (196829493379/200000000000 : ℝ) (61509216681/62500000000 : ℝ) (177352088801/1000000000000 : ℝ) (177352088807/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67023/524288 : ℝ)) (196829493379/200000000000 : ℝ) (61509216681/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67023/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196829493379/200000000000 : ℝ) (61509216681/62500000000 : ℝ) (992073733447/1000000000000 : ℝ) (124009216681/125000000000 : ℝ) (198408413823/200000000000 : ℝ) (992042069117/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67023/524288 : ℝ)) 1 (992073733447/1000000000000 : ℝ) (124009216681/125000000000 : ℝ) (198408413823/200000000000 : ℝ) (992042069117/1000000000000 : ℝ) (992057901281/1000000000000 : ℝ) (992057901283/1000000000000 : ℝ) (496028950577/500000000000 : ℝ) (992057901157/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67023/524288 : ℝ)) 2 (992057901281/1000000000000 : ℝ) (992057901283/1000000000000 : ℝ) (496028950577/500000000000 : ℝ) (992057901157/1000000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67023/524288 : ℝ)) 3 (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67023/524288 : ℝ)) 4 (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67023/524288 : ℝ)) 5 (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67023/524288 : ℝ)) 6 (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67023/524288 : ℝ)) 7 (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67023/524288 : ℝ))) (177352088801/1000000000000 : ℝ) (177352088807/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67023/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177352088801/1000000000000 : ℝ) (177352088807/1000000000000 : ℝ) (1471690111/2500000000 : ℝ) (147169011101/250000000000 : ℝ) (26320744611/62500000000 : ℝ) (52641489223/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67023/524288 : ℝ))) 1 (1471690111/2500000000 : ℝ) (147169011101/250000000000 : ℝ) (26320744611/62500000000 : ℝ) (52641489223/125000000000 : ℝ) (31556498693/62500000000 : ℝ) (252451989547/500000000000 : ℝ) (497905883849/1000000000000 : ℝ) (497905883857/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67023/524288 : ℝ))) 2 (31556498693/62500000000 : ℝ) (252451989547/500000000000 : ℝ) (497905883849/1000000000000 : ℝ) (497905883857/1000000000000 : ℝ) (125351232867/250000000000 : ℝ) (125351232869/250000000000 : ℝ) (501392722291/1000000000000 : ℝ) (501392722299/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67023/524288 : ℝ))) 3 (125351232867/250000000000 : ℝ) (125351232869/250000000000 : ℝ) (501392722291/1000000000000 : ℝ) (501392722299/1000000000000 : ℝ) (501398826879/1000000000000 : ℝ) (62674853361/125000000000 : ℝ) (250699413421/500000000000 : ℝ) (501398826851/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67023/524288 : ℝ))) 4 (501398826879/1000000000000 : ℝ) (62674853361/125000000000 : ℝ) (250699413421/500000000000 : ℝ) (501398826851/1000000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67023/524288 : ℝ))) 5 (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67023/524288 : ℝ))) 6 (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67023/524288 : ℝ))) 7 (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67023/524288 : ℝ)) hmem 8 (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67023/524288 : ℝ))) hcmem 8 (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67023/524288 : ℝ)) (992057901217/1000000000000 : ℝ) (49602895061/50000000000 : ℝ) (25069941343/50000000000 : ℝ) (50139882687/100000000000 : ℝ) (793900673057/1000000000000 : ℝ) (793900673077/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0950_exp_lower
  have heNumeric : (1027450845743/500000000000 : ℝ)/4 ≤ Real.exp (-42628246592553/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450845743/500000000000 : ℝ)/4 ≤ Real.exp ((33511/262144 : ℝ)-(793900673077/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33511/262144 : ℝ) (67023/524288 : ℝ) (793900673077/1000000000000 : ℝ) (1027450845743/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0951; no trusted numerical premise.
theorem cover8_leaf0951_exp_radius : (998004522761578417/1000000000000000000 : ℝ) ≤ Real.exp ((-4189/262144 : ℝ)/8) ∧ Real.exp ((-4189/262144 : ℝ)/8) ≤ (499002261380789209/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4189/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0951_exp_lower : (920113456824348237/1000000000000000000 : ℝ) ≤ Real.exp ((-85256492961281/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256492961281/128000000000000 : ℝ)/8) ≤ (460056728412174119/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256492961281/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0951_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901695079/1000000000000 : ℝ) ≤ 4*Real.exp (67023/524288 : ℝ)*Real.exp (-mu (radius 8 (4189/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901695079/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4189/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0951_exp_radius
  have hrNumeric : (1922162563/1953125000 : ℝ) ≤ Real.exp (-4189/262144 : ℝ) ∧ Real.exp (-4189/262144 : ℝ) ≤ (984147232257/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (1922162563/1953125000 : ℝ) ≤ (radius 8 (4189/32768 : ℝ)) ∧ (radius 8 (4189/32768 : ℝ)) ≤ (984147232257/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4189/32768 : ℝ)) (1922162563/1953125000 : ℝ) (984147232257/1000000000000 : ℝ) (35470678167/200000000000 : ℝ) (88676695421/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4189/32768 : ℝ)) (1922162563/1953125000 : ℝ) (984147232257/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4189/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (1922162563/1953125000 : ℝ) (984147232257/1000000000000 : ℝ) (3875287563/3906250000 : ℝ) (992073616129/1000000000000 : ℝ) (496020975427/500000000000 : ℝ) (124005243857/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4189/32768 : ℝ)) 1 (3875287563/3906250000 : ℝ) (992073616129/1000000000000 : ℝ) (496020975427/500000000000 : ℝ) (124005243857/125000000000 : ℝ) (992057783491/1000000000000 : ℝ) (992057783493/1000000000000 : ℝ) (248014445841/250000000000 : ℝ) (992057783367/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4189/32768 : ℝ)) 2 (992057783491/1000000000000 : ℝ) (992057783493/1000000000000 : ℝ) (248014445841/250000000000 : ℝ) (992057783367/1000000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4189/32768 : ℝ)) 3 (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4189/32768 : ℝ)) 4 (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4189/32768 : ℝ)) 5 (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4189/32768 : ℝ)) 6 (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4189/32768 : ℝ)) 7 (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4189/32768 : ℝ))) (35470678167/200000000000 : ℝ) (88676695421/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4189/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35470678167/200000000000 : ℝ) (88676695421/500000000000 : ℝ) (588676695417/1000000000000 : ℝ) (588676695421/1000000000000 : ℝ) (421133459647/1000000000000 : ℝ) (421133459657/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4189/32768 : ℝ))) 1 (588676695417/1000000000000 : ℝ) (588676695421/1000000000000 : ℝ) (421133459647/1000000000000 : ℝ) (421133459657/1000000000000 : ℝ) (126226269383/250000000000 : ℝ) (504905077539/1000000000000 : ℝ) (497907073011/1000000000000 : ℝ) (497907073019/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4189/32768 : ℝ))) 2 (126226269383/250000000000 : ℝ) (504905077539/1000000000000 : ℝ) (497907073011/1000000000000 : ℝ) (497907073019/1000000000000 : ℝ) (501406075271/1000000000000 : ℝ) (501406075279/1000000000000 : ℝ) (250696933219/500000000000 : ℝ) (501393866447/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4189/32768 : ℝ))) 3 (501406075271/1000000000000 : ℝ) (501406075279/1000000000000 : ℝ) (250696933219/500000000000 : ℝ) (501393866447/1000000000000 : ℝ) (250699985427/500000000000 : ℝ) (501399970863/1000000000000 : ℝ) (501399970817/1000000000000 : ℝ) (250699985413/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4189/32768 : ℝ))) 4 (250699985427/500000000000 : ℝ) (501399970863/1000000000000 : ℝ) (501399970817/1000000000000 : ℝ) (250699985413/500000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4189/32768 : ℝ))) 5 (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4189/32768 : ℝ))) 6 (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4189/32768 : ℝ))) 7 (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4189/32768 : ℝ)) hmem 8 (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4189/32768 : ℝ))) hcmem 8 (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4189/32768 : ℝ)) (992057783427/1000000000000 : ℝ) (99205778343/100000000000 : ℝ) (100279994167/200000000000 : ℝ) (100279994169/200000000000 : ℝ) (793902578657/1000000000000 : ℝ) (793902578677/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0951_exp_lower
  have heNumeric : (2054901695079/1000000000000 : ℝ)/4 ≤ Real.exp (-85256492961281/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901695079/1000000000000 : ℝ)/4 ≤ Real.exp ((67023/524288 : ℝ)-(793902578677/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67023/524288 : ℝ) (4189/32768 : ℝ) (793902578677/1000000000000 : ℝ) (2054901695079/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0952; no trusted numerical premise.
theorem cover8_leaf0952_exp_radius : (998004493018726329/1000000000000000000 : ℝ) ≤ Real.exp ((-67025/4194304 : ℝ)/8) ∧ Real.exp ((-67025/4194304 : ℝ)/8) ≤ (99800449301872633/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67025/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0952_exp_lower : (23002836425691277/25000000000000000 : ℝ) ≤ Real.exp ((-5328530795939/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328530795939/8000000000000 : ℝ)/8) ≤ (920113457027651081/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328530795939/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0952_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862712339/125000000000 : ℝ) ≤ 4*Real.exp (4189/32768 : ℝ)*Real.exp (-mu (radius 8 (67025/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862712339/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67025/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0952_exp_radius
  have hrNumeric : (984146997617/1000000000000 : ℝ) ≤ Real.exp (-67025/4194304 : ℝ) ∧ Real.exp (-67025/4194304 : ℝ) ≤ (492073498809/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984146997617/1000000000000 : ℝ) ≤ (radius 8 (67025/524288 : ℝ)) ∧ (radius 8 (67025/524288 : ℝ)) ≤ (492073498809/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67025/524288 : ℝ)) (984146997617/1000000000000 : ℝ) (492073498809/500000000000 : ℝ) (8867734643/50000000000 : ℝ) (88677346433/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67025/524288 : ℝ)) (984146997617/1000000000000 : ℝ) (492073498809/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67025/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984146997617/1000000000000 : ℝ) (492073498809/500000000000 : ℝ) (124009187351/125000000000 : ℝ) (992073498809/1000000000000 : ℝ) (496020916297/500000000000 : ℝ) (198408366519/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67025/524288 : ℝ)) 1 (124009187351/125000000000 : ℝ) (992073498809/1000000000000 : ℝ) (496020916297/500000000000 : ℝ) (198408366519/200000000000 : ℝ) (992057665701/1000000000000 : ℝ) (496028832851/500000000000 : ℝ) (496028832787/500000000000 : ℝ) (124007208197/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67025/524288 : ℝ)) 2 (992057665701/1000000000000 : ℝ) (496028832851/500000000000 : ℝ) (496028832787/500000000000 : ℝ) (124007208197/125000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67025/524288 : ℝ)) 3 (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67025/524288 : ℝ)) 4 (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67025/524288 : ℝ)) 5 (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67025/524288 : ℝ)) 6 (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67025/524288 : ℝ)) 7 (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67025/524288 : ℝ))) (8867734643/50000000000 : ℝ) (88677346433/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67025/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8867734643/50000000000 : ℝ) (88677346433/500000000000 : ℝ) (58867734643/100000000000 : ℝ) (588677346433/1000000000000 : ℝ) (210567502751/500000000000 : ℝ) (421135005511/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67025/524288 : ℝ))) 1 (58867734643/100000000000 : ℝ) (588677346433/1000000000000 : ℝ) (210567502751/500000000000 : ℝ) (421135005511/1000000000000 : ℝ) (252453087983/500000000000 : ℝ) (126226543993/250000000000 : ℝ) (6223853277/12500000000 : ℝ) (62238532771/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67025/524288 : ℝ))) 2 (252453087983/500000000000 : ℝ) (126226543993/250000000000 : ℝ) (6223853277/12500000000 : ℝ) (62238532771/125000000000 : ℝ) (501407219063/1000000000000 : ℝ) (50140721907/100000000000 : ℝ) (250697505287/500000000000 : ℝ) (250697505291/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67025/524288 : ℝ))) 3 (501407219063/1000000000000 : ℝ) (50140721907/100000000000 : ℝ) (250697505287/500000000000 : ℝ) (250697505291/500000000000 : ℝ) (250700557409/500000000000 : ℝ) (250700557413/500000000000 : ℝ) (501401114781/1000000000000 : ℝ) (501401114789/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67025/524288 : ℝ))) 4 (250700557409/500000000000 : ℝ) (250700557413/500000000000 : ℝ) (501401114781/1000000000000 : ℝ) (501401114789/1000000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67025/524288 : ℝ))) 5 (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67025/524288 : ℝ))) 6 (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67025/524288 : ℝ))) 7 (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67025/524288 : ℝ)) hmem 8 (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67025/524288 : ℝ))) hcmem 8 (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67025/524288 : ℝ)) (992057665637/1000000000000 : ℝ) (992057665639/1000000000000 : ℝ) (501401114799/1000000000000 : ℝ) (62675139351/125000000000 : ℝ) (793904484241/1000000000000 : ℝ) (396952242129/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0952_exp_lower
  have heNumeric : (256862712339/125000000000 : ℝ)/4 ≤ Real.exp (-5328530795939/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862712339/125000000000 : ℝ)/4 ≤ Real.exp ((4189/32768 : ℝ)-(396952242129/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4189/32768 : ℝ) (67025/524288 : ℝ) (396952242129/500000000000 : ℝ) (256862712339/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0953; no trusted numerical premise.
theorem cover8_leaf0953_exp_radius : (998004463275875127/1000000000000000000 : ℝ) ≤ Real.exp ((-33513/2097152 : ℝ)/8) ∧ Real.exp ((-33513/2097152 : ℝ)/8) ≤ (124750557909484391/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33513/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0953_exp_lower : (920113457233024177/1000000000000000000 : ℝ) ≤ Real.exp ((-85256492506463/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256492506463/128000000000000 : ℝ)/8) ≤ (460056728616512089/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256492506463/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0953_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901702381/1000000000000 : ℝ) ≤ 4*Real.exp (67025/524288 : ℝ)*Real.exp (-mu (radius 8 (33513/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901702381/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33513/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0953_exp_radius
  have hrNumeric : (492073381489/500000000000 : ℝ) ≤ Real.exp (-33513/2097152 : ℝ) ∧ Real.exp (-33513/2097152 : ℝ) ≤ (984146762979/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492073381489/500000000000 : ℝ) ≤ (radius 8 (33513/262144 : ℝ)) ∧ (radius 8 (33513/262144 : ℝ)) ≤ (984146762979/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33513/262144 : ℝ)) (492073381489/500000000000 : ℝ) (984146762979/1000000000000 : ℝ) (88677997437/500000000000 : ℝ) (177355994881/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33513/262144 : ℝ)) (492073381489/500000000000 : ℝ) (984146762979/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33513/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492073381489/500000000000 : ℝ) (984146762979/1000000000000 : ℝ) (992073381489/1000000000000 : ℝ) (99207338149/100000000000 : ℝ) (992041714333/1000000000000 : ℝ) (198408342867/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33513/262144 : ℝ)) 1 (992073381489/1000000000000 : ℝ) (99207338149/100000000000 : ℝ) (992041714333/1000000000000 : ℝ) (198408342867/200000000000 : ℝ) (992057547911/1000000000000 : ℝ) (992057547913/1000000000000 : ℝ) (124007193473/125000000000 : ℝ) (992057547787/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33513/262144 : ℝ)) 2 (992057547911/1000000000000 : ℝ) (992057547913/1000000000000 : ℝ) (124007193473/125000000000 : ℝ) (992057547787/1000000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33513/262144 : ℝ)) 3 (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33513/262144 : ℝ)) 4 (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33513/262144 : ℝ)) 5 (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33513/262144 : ℝ)) 6 (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33513/262144 : ℝ)) 7 (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33513/262144 : ℝ))) (88677997437/500000000000 : ℝ) (177355994881/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33513/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88677997437/500000000000 : ℝ) (177355994881/1000000000000 : ℝ) (588677997437/1000000000000 : ℝ) (588677997441/1000000000000 : ℝ) (421136551339/1000000000000 : ℝ) (105284137837/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33513/262144 : ℝ))) 1 (588677997437/1000000000000 : ℝ) (588677997441/1000000000000 : ℝ) (421136551339/1000000000000 : ℝ) (105284137837/250000000000 : ℝ) (126226818597/250000000000 : ℝ) (100981454879/200000000000 : ℝ) (99581890259/200000000000 : ℝ) (497909451303/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33513/262144 : ℝ))) 2 (126226818597/250000000000 : ℝ) (100981454879/200000000000 : ℝ) (99581890259/200000000000 : ℝ) (497909451303/1000000000000 : ℝ) (501408362841/1000000000000 : ℝ) (501408362849/1000000000000 : ℝ) (501396154697/1000000000000 : ℝ) (100279230941/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33513/262144 : ℝ))) 3 (501408362841/1000000000000 : ℝ) (501408362849/1000000000000 : ℝ) (501396154697/1000000000000 : ℝ) (100279230941/200000000000 : ℝ) (501402258769/1000000000000 : ℝ) (501402258777/1000000000000 : ℝ) (501402258731/1000000000000 : ℝ) (25070112937/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33513/262144 : ℝ))) 4 (501402258769/1000000000000 : ℝ) (501402258777/1000000000000 : ℝ) (501402258731/1000000000000 : ℝ) (25070112937/50000000000 : ℝ) (401121807/800000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33513/262144 : ℝ))) 5 (401121807/800000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33513/262144 : ℝ))) 6 (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33513/262144 : ℝ))) 7 (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33513/262144 : ℝ)) hmem 8 (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33513/262144 : ℝ))) hcmem 8 (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33513/262144 : ℝ)) (992057547847/1000000000000 : ℝ) (19841150957/20000000000 : ℝ) (501402258749/1000000000000 : ℝ) (501402258759/1000000000000 : ℝ) (396953194901/500000000000 : ℝ) (793906389821/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0953_exp_lower
  have heNumeric : (2054901702381/1000000000000 : ℝ)/4 ≤ Real.exp (-85256492506463/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901702381/1000000000000 : ℝ)/4 ≤ Real.exp ((67025/524288 : ℝ)-(793906389821/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67025/524288 : ℝ) (33513/262144 : ℝ) (793906389821/1000000000000 : ℝ) (2054901702381/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0954; no trusted numerical premise.
theorem cover8_leaf0954_exp_radius : (998004433533024811/1000000000000000000 : ℝ) ≤ Real.exp ((-67027/4194304 : ℝ)/8) ∧ Real.exp ((-67027/4194304 : ℝ)/8) ≤ (249501108383256203/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67027/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0954_exp_lower : (92011345744046753/100000000000000000 : ℝ) ≤ Real.exp ((-42628246137799/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628246137799/64000000000000 : ℝ)/8) ≤ (920113457440467531/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628246137799/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0954_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901706087/1000000000000 : ℝ) ≤ 4*Real.exp (33513/262144 : ℝ)*Real.exp (-mu (radius 8 (67027/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901706087/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67027/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0954_exp_radius
  have hrNumeric : (984146528339/1000000000000 : ℝ) ≤ Real.exp (-67027/4194304 : ℝ) ∧ Real.exp (-67027/4194304 : ℝ) ≤ (49207326417/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984146528339/1000000000000 : ℝ) ≤ (radius 8 (67027/524288 : ℝ)) ∧ (radius 8 (67027/524288 : ℝ)) ≤ (49207326417/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67027/524288 : ℝ)) (984146528339/1000000000000 : ℝ) (49207326417/50000000000 : ℝ) (177357296879/1000000000000 : ℝ) (35471459377/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67027/524288 : ℝ)) (984146528339/1000000000000 : ℝ) (49207326417/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67027/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984146528339/1000000000000 : ℝ) (49207326417/50000000000 : ℝ) (992073264169/1000000000000 : ℝ) (99207326417/100000000000 : ℝ) (124005199509/125000000000 : ℝ) (496020798037/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67027/524288 : ℝ)) 1 (992073264169/1000000000000 : ℝ) (99207326417/100000000000 : ℝ) (124005199509/125000000000 : ℝ) (496020798037/500000000000 : ℝ) (24801435753/25000000000 : ℝ) (496028715061/500000000000 : ℝ) (496028714997/500000000000 : ℝ) (248014357499/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67027/524288 : ℝ)) 2 (24801435753/25000000000 : ℝ) (496028715061/500000000000 : ℝ) (496028714997/500000000000 : ℝ) (248014357499/250000000000 : ℝ) (992057430057/1000000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67027/524288 : ℝ)) 3 (992057430057/1000000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67027/524288 : ℝ)) 4 (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67027/524288 : ℝ)) 5 (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67027/524288 : ℝ)) 6 (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67027/524288 : ℝ)) 7 (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67027/524288 : ℝ))) (177357296879/1000000000000 : ℝ) (35471459377/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67027/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177357296879/1000000000000 : ℝ) (35471459377/200000000000 : ℝ) (588678648439/1000000000000 : ℝ) (588678648443/1000000000000 : ℝ) (421138097159/1000000000000 : ℝ) (421138097167/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67027/524288 : ℝ))) 1 (588678648439/1000000000000 : ℝ) (588678648443/1000000000000 : ℝ) (421138097159/1000000000000 : ℝ) (421138097167/1000000000000 : ℝ) (504908372799/1000000000000 : ℝ) (100981674561/200000000000 : ℝ) (248955320209/500000000000 : ℝ) (19916425617/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67027/524288 : ℝ))) 2 (504908372799/1000000000000 : ℝ) (100981674561/200000000000 : ℝ) (248955320209/500000000000 : ℝ) (19916425617/40000000000 : ℝ) (31338094163/62500000000 : ℝ) (100281901323/200000000000 : ℝ) (62674662351/125000000000 : ℝ) (3917166397/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67027/524288 : ℝ))) 3 (31338094163/62500000000 : ℝ) (100281901323/200000000000 : ℝ) (62674662351/125000000000 : ℝ) (3917166397/7812500000 : ℝ) (125350850677/250000000000 : ℝ) (125350850679/250000000000 : ℝ) (50140340267/100000000000 : ℝ) (501403402679/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67027/524288 : ℝ))) 4 (125350850677/250000000000 : ℝ) (125350850679/250000000000 : ℝ) (50140340267/100000000000 : ℝ) (501403402679/1000000000000 : ℝ) (501403402689/1000000000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67027/524288 : ℝ))) 5 (501403402689/1000000000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67027/524288 : ℝ))) 6 (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67027/524288 : ℝ))) 7 (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67027/524288 : ℝ)) hmem 8 (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67027/524288 : ℝ))) hcmem 8 (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67027/524288 : ℝ)) (124007178757/125000000000 : ℝ) (992057430059/1000000000000 : ℝ) (7834428167/15625000000 : ℝ) (250701701349/500000000000 : ℝ) (793908295347/1000000000000 : ℝ) (396954147683/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0954_exp_lower
  have heNumeric : (2054901706087/1000000000000 : ℝ)/4 ≤ Real.exp (-42628246137799/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901706087/1000000000000 : ℝ)/4 ≤ Real.exp ((33513/262144 : ℝ)-(396954147683/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33513/262144 : ℝ) (67027/524288 : ℝ) (396954147683/500000000000 : ℝ) (2054901706087/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0955; no trusted numerical premise.
theorem cover8_leaf0955_exp_radius : (499002201895087691/500000000000000000 : ℝ) ≤ Real.exp ((-16757/1048576 : ℝ)/8) ∧ Real.exp ((-16757/1048576 : ℝ)/8) ≤ (998004403790175383/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16757/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0955_exp_lower : (230028364412725313/250000000000000000 : ℝ) ≤ Real.exp ((-17051298408281/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051298408281/25600000000000 : ℝ)/8) ≤ (920113457650901253/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051298408281/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0955_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901709847/1000000000000 : ℝ) ≤ 4*Real.exp (67027/524288 : ℝ)*Real.exp (-mu (radius 8 (16757/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901709847/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16757/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0955_exp_radius
  have hrNumeric : (984146293701/1000000000000 : ℝ) ≤ Real.exp (-16757/1048576 : ℝ) ∧ Real.exp (-16757/1048576 : ℝ) ≤ (492073146851/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984146293701/1000000000000 : ℝ) ≤ (radius 8 (16757/131072 : ℝ)) ∧ (radius 8 (16757/131072 : ℝ)) ≤ (492073146851/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16757/131072 : ℝ)) (984146293701/1000000000000 : ℝ) (492073146851/500000000000 : ℝ) (44339649717/250000000000 : ℝ) (1418868791/8000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16757/131072 : ℝ)) (984146293701/1000000000000 : ℝ) (492073146851/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16757/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984146293701/1000000000000 : ℝ) (492073146851/500000000000 : ℝ) (19841462937/20000000000 : ℝ) (992073146851/1000000000000 : ℝ) (248010369453/250000000000 : ℝ) (496020738907/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16757/131072 : ℝ)) 1 (19841462937/20000000000 : ℝ) (992073146851/1000000000000 : ℝ) (248010369453/250000000000 : ℝ) (496020738907/500000000000 : ℝ) (992057312331/1000000000000 : ℝ) (992057312333/1000000000000 : ℝ) (248014328051/250000000000 : ℝ) (992057312207/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16757/131072 : ℝ)) 2 (992057312331/1000000000000 : ℝ) (992057312333/1000000000000 : ℝ) (248014328051/250000000000 : ℝ) (992057312207/1000000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16757/131072 : ℝ)) 3 (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16757/131072 : ℝ)) 4 (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16757/131072 : ℝ)) 5 (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16757/131072 : ℝ)) 6 (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16757/131072 : ℝ)) 7 (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16757/131072 : ℝ))) (44339649717/250000000000 : ℝ) (1418868791/8000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16757/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44339649717/250000000000 : ℝ) (1418868791/8000000000 : ℝ) (294339649717/500000000000 : ℝ) (294339649719/500000000000 : ℝ) (210569821477/500000000000 : ℝ) (421139642963/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16757/131072 : ℝ))) 1 (294339649717/500000000000 : ℝ) (294339649719/500000000000 : ℝ) (210569821477/500000000000 : ℝ) (421139642963/1000000000000 : ℝ) (252454735597/500000000000 : ℝ) (504909471201/1000000000000 : ℝ) (248955914761/500000000000 : ℝ) (49791182953/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16757/131072 : ℝ))) 2 (252454735597/500000000000 : ℝ) (504909471201/1000000000000 : ℝ) (248955914761/500000000000 : ℝ) (49791182953/100000000000 : ℝ) (250705325179/500000000000 : ℝ) (250705325183/500000000000 : ℝ) (250699221451/500000000000 : ℝ) (501398442911/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16757/131072 : ℝ))) 3 (250705325179/500000000000 : ℝ) (250705325183/500000000000 : ℝ) (250699221451/500000000000 : ℝ) (501398442911/1000000000000 : ℝ) (50140454663/100000000000 : ℝ) (501404546639/1000000000000 : ℝ) (15668892081/31250000000 : ℝ) (250702273301/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16757/131072 : ℝ))) 4 (50140454663/100000000000 : ℝ) (501404546639/1000000000000 : ℝ) (15668892081/31250000000 : ℝ) (250702273301/500000000000 : ℝ) (501404546611/1000000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16757/131072 : ℝ))) 5 (501404546611/1000000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16757/131072 : ℝ))) 6 (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16757/131072 : ℝ))) 7 (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16757/131072 : ℝ)) hmem 8 (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16757/131072 : ℝ))) hcmem 8 (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16757/131072 : ℝ)) (992057312267/1000000000000 : ℝ) (99205731227/100000000000 : ℝ) (50140454661/100000000000 : ℝ) (501404546621/1000000000000 : ℝ) (24809693777/31250000000 : ℝ) (158782040177/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0955_exp_lower
  have heNumeric : (2054901709847/1000000000000 : ℝ)/4 ≤ Real.exp (-17051298408281/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901709847/1000000000000 : ℝ)/4 ≤ Real.exp ((67027/524288 : ℝ)-(158782040177/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67027/524288 : ℝ) (16757/131072 : ℝ) (158782040177/200000000000 : ℝ) (2054901709847/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0956; no trusted numerical premise.
theorem cover8_leaf0956_exp_radius : (998004374047326839/1000000000000000000 : ℝ) ≤ Real.exp ((-67029/4194304 : ℝ)/8) ∧ Real.exp ((-67029/4194304 : ℝ)/8) ≤ (24950109351183171/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67029/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0956_exp_lower : (460056728931530093/500000000000000000 : ℝ) ≤ Real.exp ((-21314122951323/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314122951323/32000000000000 : ℝ)/8) ≤ (920113457863060187/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314122951323/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0956_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450856819/500000000000 : ℝ) ≤ 4*Real.exp (16757/131072 : ℝ)*Real.exp (-mu (radius 8 (67029/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450856819/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67029/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0956_exp_radius
  have hrNumeric : (492073029531/500000000000 : ℝ) ≤ Real.exp (-67029/4194304 : ℝ) ∧ Real.exp (-67029/4194304 : ℝ) ≤ (984146059063/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492073029531/500000000000 : ℝ) ≤ (radius 8 (67029/524288 : ℝ)) ∧ (radius 8 (67029/524288 : ℝ)) ≤ (984146059063/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67029/524288 : ℝ)) (492073029531/500000000000 : ℝ) (984146059063/1000000000000 : ℝ) (177359900853/1000000000000 : ℝ) (8867995043/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67029/524288 : ℝ)) (492073029531/500000000000 : ℝ) (984146059063/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67029/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492073029531/500000000000 : ℝ) (984146059063/1000000000000 : ℝ) (992073029531/1000000000000 : ℝ) (248018257383/250000000000 : ℝ) (15500646243/15625000000 : ℝ) (992041359553/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67029/524288 : ℝ)) 1 (992073029531/1000000000000 : ℝ) (248018257383/250000000000 : ℝ) (15500646243/15625000000 : ℝ) (992041359553/1000000000000 : ℝ) (992057194541/1000000000000 : ℝ) (992057194543/1000000000000 : ℝ) (198411438883/200000000000 : ℝ) (992057194417/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67029/524288 : ℝ)) 2 (992057194541/1000000000000 : ℝ) (992057194543/1000000000000 : ℝ) (198411438883/200000000000 : ℝ) (992057194417/1000000000000 : ℝ) (496028597239/500000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67029/524288 : ℝ)) 3 (496028597239/500000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67029/524288 : ℝ)) 4 (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67029/524288 : ℝ)) 5 (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67029/524288 : ℝ)) 6 (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67029/524288 : ℝ)) 7 (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67029/524288 : ℝ))) (177359900853/1000000000000 : ℝ) (8867995043/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67029/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177359900853/1000000000000 : ℝ) (8867995043/50000000000 : ℝ) (294339975213/500000000000 : ℝ) (58867995043/100000000000 : ℝ) (421141188739/1000000000000 : ℝ) (105285297187/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67029/524288 : ℝ))) 1 (294339975213/500000000000 : ℝ) (58867995043/100000000000 : ℝ) (421141188739/1000000000000 : ℝ) (105285297187/250000000000 : ℝ) (252455284791/500000000000 : ℝ) (504910569589/1000000000000 : ℝ) (497913018617/1000000000000 : ℝ) (3983304149/8000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67029/524288 : ℝ))) 2 (252455284791/500000000000 : ℝ) (504910569589/1000000000000 : ℝ) (497913018617/1000000000000 : ℝ) (3983304149/8000000000 : ℝ) (501411794099/1000000000000 : ℝ) (501411794107/1000000000000 : ℝ) (125349896747/250000000000 : ℝ) (125349896749/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67029/524288 : ℝ))) 3 (501411794099/1000000000000 : ℝ) (501411794107/1000000000000 : ℝ) (125349896747/250000000000 : ℝ) (125349896749/250000000000 : ℝ) (501405690543/1000000000000 : ℝ) (62675711319/125000000000 : ℝ) (250702845253/500000000000 : ℝ) (100281138103/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67029/524288 : ℝ))) 4 (501405690543/1000000000000 : ℝ) (62675711319/125000000000 : ℝ) (250702845253/500000000000 : ℝ) (100281138103/200000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67029/524288 : ℝ))) 5 (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67029/524288 : ℝ))) 6 (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67029/524288 : ℝ))) 7 (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67029/524288 : ℝ)) hmem 8 (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67029/524288 : ℝ))) hcmem 8 (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67029/524288 : ℝ)) (992057194477/1000000000000 : ℝ) (12400714931/12500000000 : ℝ) (125351422631/250000000000 : ℝ) (250702845267/500000000000 : ℝ) (79391210637/100000000000 : ℝ) (793912106389/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0956_exp_lower
  have heNumeric : (1027450856819/500000000000 : ℝ)/4 ≤ Real.exp (-21314122951323/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450856819/500000000000 : ℝ)/4 ≤ Real.exp ((16757/131072 : ℝ)-(793912106389/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16757/131072 : ℝ) (67029/524288 : ℝ) (793912106389/1000000000000 : ℝ) (1027450856819/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0957; no trusted numerical premise.
theorem cover8_leaf0957_exp_radius : (499002172152239591/500000000000000000 : ℝ) ≤ Real.exp ((-33515/2097152 : ℝ)/8) ∧ Real.exp ((-33515/2097152 : ℝ)/8) ≤ (998004344304479183/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33515/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0957_exp_lower : (230028364519264837/250000000000000000 : ℝ) ≤ Real.exp ((-85256491567131/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256491567131/128000000000000 : ℝ)/8) ≤ (920113458077059349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256491567131/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0957_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901717461/1000000000000 : ℝ) ≤ 4*Real.exp (67029/524288 : ℝ)*Real.exp (-mu (radius 8 (33515/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901717461/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33515/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0957_exp_radius
  have hrNumeric : (984145824423/1000000000000 : ℝ) ≤ Real.exp (-33515/2097152 : ℝ) ∧ Real.exp (-33515/2097152 : ℝ) ≤ (123018228053/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984145824423/1000000000000 : ℝ) ≤ (radius 8 (33515/262144 : ℝ)) ∧ (radius 8 (33515/262144 : ℝ)) ≤ (123018228053/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33515/262144 : ℝ)) (984145824423/1000000000000 : ℝ) (123018228053/125000000000 : ℝ) (44340300707/250000000000 : ℝ) (35472240567/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33515/262144 : ℝ)) (984145824423/1000000000000 : ℝ) (123018228053/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33515/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984145824423/1000000000000 : ℝ) (123018228053/125000000000 : ℝ) (992072912211/1000000000000 : ℝ) (248018228053/250000000000 : ℝ) (992041241291/1000000000000 : ℝ) (248010310323/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33515/262144 : ℝ)) 1 (992072912211/1000000000000 : ℝ) (248018228053/250000000000 : ℝ) (992041241291/1000000000000 : ℝ) (248010310323/250000000000 : ℝ) (992057076751/1000000000000 : ℝ) (62003567297/62500000000 : ℝ) (62003567289/62500000000 : ℝ) (496028538313/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33515/262144 : ℝ)) 2 (992057076751/1000000000000 : ℝ) (62003567297/62500000000 : ℝ) (62003567289/62500000000 : ℝ) (496028538313/500000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33515/262144 : ℝ)) 3 (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33515/262144 : ℝ)) 4 (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33515/262144 : ℝ)) 5 (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33515/262144 : ℝ)) 6 (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33515/262144 : ℝ)) 7 (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33515/262144 : ℝ))) (44340300707/250000000000 : ℝ) (35472240567/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33515/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44340300707/250000000000 : ℝ) (35472240567/200000000000 : ℝ) (294340300707/500000000000 : ℝ) (294340300709/500000000000 : ℝ) (210571367253/500000000000 : ℝ) (105285683629/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33515/262144 : ℝ))) 1 (294340300707/500000000000 : ℝ) (294340300709/500000000000 : ℝ) (210571367253/500000000000 : ℝ) (105285683629/250000000000 : ℝ) (12622791699/25000000000 : ℝ) (504911667967/1000000000000 : ℝ) (4979142077/10000000000 : ℝ) (497914207709/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33515/262144 : ℝ))) 2 (12622791699/25000000000 : ℝ) (504911667967/1000000000000 : ℝ) (4979142077/10000000000 : ℝ) (497914207709/1000000000000 : ℝ) (50141293783/100000000000 : ℝ) (250706468919/500000000000 : ℝ) (501400731063/1000000000000 : ℝ) (7834386423/15625000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33515/262144 : ℝ))) 3 (50141293783/100000000000 : ℝ) (250706468919/500000000000 : ℝ) (501400731063/1000000000000 : ℝ) (7834386423/15625000000 : ℝ) (250703417223/500000000000 : ℝ) (100281366891/200000000000 : ℝ) (501406834409/1000000000000 : ℝ) (250703417209/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33515/262144 : ℝ))) 4 (250703417223/500000000000 : ℝ) (100281366891/200000000000 : ℝ) (501406834409/1000000000000 : ℝ) (250703417209/500000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33515/262144 : ℝ))) 5 (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33515/262144 : ℝ))) 6 (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33515/262144 : ℝ))) 7 (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33515/262144 : ℝ)) hmem 8 (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33515/262144 : ℝ))) hcmem 8 (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33515/262144 : ℝ)) (992057076687/1000000000000 : ℝ) (992057076689/1000000000000 : ℝ) (501406834427/1000000000000 : ℝ) (501406834437/1000000000000 : ℝ) (793914011859/1000000000000 : ℝ) (793914011877/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0957_exp_lower
  have heNumeric : (2054901717461/1000000000000 : ℝ)/4 ≤ Real.exp (-85256491567131/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901717461/1000000000000 : ℝ)/4 ≤ Real.exp ((67029/524288 : ℝ)-(793914011877/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67029/524288 : ℝ) (33515/262144 : ℝ) (793914011877/1000000000000 : ℝ) (2054901717461/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0958; no trusted numerical premise.
theorem cover8_leaf0958_exp_radius : (249501078640408103/250000000000000000 : ℝ) ≤ Real.exp ((-67031/4194304 : ℝ)/8) ∧ Real.exp ((-67031/4194304 : ℝ)/8) ≤ (998004314561632413/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67031/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0958_exp_lower : (460056729147139453/500000000000000000 : ℝ) ≤ Real.exp ((-42628245662693/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628245662693/64000000000000 : ℝ)/8) ≤ (920113458294278907/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628245662693/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0958_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450860671/500000000000 : ℝ) ≤ 4*Real.exp (33515/262144 : ℝ)*Real.exp (-mu (radius 8 (67031/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450860671/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67031/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0958_exp_radius
  have hrNumeric : (196829117957/200000000000 : ℝ) ≤ Real.exp (-67031/4194304 : ℝ) ∧ Real.exp (-67031/4194304 : ℝ) ≤ (492072794893/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196829117957/200000000000 : ℝ) ≤ (radius 8 (67031/524288 : ℝ)) ∧ (radius 8 (67031/524288 : ℝ)) ≤ (492072794893/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67031/524288 : ℝ)) (196829117957/200000000000 : ℝ) (492072794893/500000000000 : ℝ) (44340626197/250000000000 : ℝ) (88681252397/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67031/524288 : ℝ)) (196829117957/200000000000 : ℝ) (492072794893/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67031/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196829117957/200000000000 : ℝ) (492072794893/500000000000 : ℝ) (248018198723/250000000000 : ℝ) (992072794893/1000000000000 : ℝ) (992041123031/1000000000000 : ℝ) (124005140379/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67031/524288 : ℝ)) 1 (248018198723/250000000000 : ℝ) (992072794893/1000000000000 : ℝ) (992041123031/1000000000000 : ℝ) (124005140379/125000000000 : ℝ) (992056958961/1000000000000 : ℝ) (992056958963/1000000000000 : ℝ) (198411391767/200000000000 : ℝ) (992056958837/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67031/524288 : ℝ)) 2 (992056958961/1000000000000 : ℝ) (992056958963/1000000000000 : ℝ) (198411391767/200000000000 : ℝ) (992056958837/1000000000000 : ℝ) (496028479449/500000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67031/524288 : ℝ)) 3 (496028479449/500000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67031/524288 : ℝ)) 4 (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67031/524288 : ℝ)) 5 (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67031/524288 : ℝ)) 6 (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67031/524288 : ℝ)) 7 (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67031/524288 : ℝ))) (44340626197/250000000000 : ℝ) (88681252397/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67031/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44340626197/250000000000 : ℝ) (88681252397/500000000000 : ℝ) (294340626197/500000000000 : ℝ) (588681252397/1000000000000 : ℝ) (1684577121/4000000000 : ℝ) (210572140129/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67031/524288 : ℝ))) 1 (294340626197/500000000000 : ℝ) (588681252397/1000000000000 : ℝ) (1684577121/4000000000 : ℝ) (210572140129/500000000000 : ℝ) (252456383161/500000000000 : ℝ) (63114095791/125000000000 : ℝ) (99583079353/200000000000 : ℝ) (124478849193/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67031/524288 : ℝ))) 2 (252456383161/500000000000 : ℝ) (63114095791/125000000000 : ℝ) (99583079353/200000000000 : ℝ) (124478849193/250000000000 : ℝ) (501414081543/1000000000000 : ℝ) (10028281631/20000000000 : ℝ) (501401875121/1000000000000 : ℝ) (62675234391/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67031/524288 : ℝ))) 3 (501414081543/1000000000000 : ℝ) (10028281631/20000000000 : ℝ) (501401875121/1000000000000 : ℝ) (62675234391/125000000000 : ℝ) (125351994583/250000000000 : ℝ) (501407978339/1000000000000 : ℝ) (250703989147/500000000000 : ℝ) (250703989151/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67031/524288 : ℝ))) 4 (125351994583/250000000000 : ℝ) (501407978339/1000000000000 : ℝ) (250703989147/500000000000 : ℝ) (250703989151/500000000000 : ℝ) (501407978313/1000000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67031/524288 : ℝ))) 5 (501407978313/1000000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67031/524288 : ℝ))) 6 (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67031/524288 : ℝ))) 7 (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67031/524288 : ℝ)) hmem 8 (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67031/524288 : ℝ))) hcmem 8 (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67031/524288 : ℝ)) (992056958897/1000000000000 : ℝ) (9920569589/10000000000 : ℝ) (62675997289/125000000000 : ℝ) (501407978321/1000000000000 : ℝ) (793915917319/1000000000000 : ℝ) (793915917337/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0958_exp_lower
  have heNumeric : (1027450860671/500000000000 : ℝ)/4 ≤ Real.exp (-42628245662693/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450860671/500000000000 : ℝ)/4 ≤ Real.exp ((33515/262144 : ℝ)-(793915917337/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33515/262144 : ℝ) (67031/524288 : ℝ) (793915917337/1000000000000 : ℝ) (1027450860671/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0959; no trusted numerical premise.
theorem cover8_leaf0959_exp_radius : (998004284818786529/1000000000000000000 : ℝ) ≤ Real.exp ((-8379/524288 : ℝ)/8) ∧ Real.exp ((-8379/524288 : ℝ)/8) ≤ (99800428481878653/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8379/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0959_exp_lower : (115014182314066699/125000000000000000 : ℝ) ≤ Real.exp ((-85256491082489/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256491082489/128000000000000 : ℝ)/8) ≤ (920113458512533593/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256491082489/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0959_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901725241/1000000000000 : ℝ) ≤ 4*Real.exp (67031/524288 : ℝ)*Real.exp (-mu (radius 8 (8379/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901725241/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8379/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0959_exp_radius
  have hrNumeric : (492072677573/500000000000 : ℝ) ≤ Real.exp (-8379/524288 : ℝ) ∧ Real.exp (-8379/524288 : ℝ) ≤ (984145355147/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492072677573/500000000000 : ℝ) ≤ (radius 8 (8379/65536 : ℝ)) ∧ (radius 8 (8379/65536 : ℝ)) ≤ (984145355147/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8379/65536 : ℝ)) (492072677573/500000000000 : ℝ) (984145355147/1000000000000 : ℝ) (177363806743/1000000000000 : ℝ) (709455227/4000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8379/65536 : ℝ)) (492072677573/500000000000 : ℝ) (984145355147/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8379/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492072677573/500000000000 : ℝ) (984145355147/1000000000000 : ℝ) (992072677573/1000000000000 : ℝ) (496036338787/500000000000 : ℝ) (99204100477/100000000000 : ℝ) (992041004771/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8379/65536 : ℝ)) 1 (992072677573/1000000000000 : ℝ) (496036338787/500000000000 : ℝ) (99204100477/100000000000 : ℝ) (992041004771/1000000000000 : ℝ) (992056841171/1000000000000 : ℝ) (992056841173/1000000000000 : ℝ) (198411368209/200000000000 : ℝ) (992056841047/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8379/65536 : ℝ)) 2 (992056841171/1000000000000 : ℝ) (992056841173/1000000000000 : ℝ) (198411368209/200000000000 : ℝ) (992056841047/1000000000000 : ℝ) (248014210277/250000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8379/65536 : ℝ)) 3 (248014210277/250000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8379/65536 : ℝ)) 4 (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8379/65536 : ℝ)) 5 (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8379/65536 : ℝ)) 6 (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8379/65536 : ℝ)) 7 (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8379/65536 : ℝ))) (177363806743/1000000000000 : ℝ) (709455227/4000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8379/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177363806743/1000000000000 : ℝ) (709455227/4000000000 : ℝ) (588681903371/1000000000000 : ℝ) (4709455227/8000000000 : ℝ) (421145825983/1000000000000 : ℝ) (52643228249/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8379/65536 : ℝ))) 1 (588681903371/1000000000000 : ℝ) (4709455227/8000000000 : ℝ) (421145825983/1000000000000 : ℝ) (52643228249/125000000000 : ℝ) (504913864677/1000000000000 : ℝ) (126228466171/250000000000 : ℝ) (497916585821/1000000000000 : ℝ) (497916585829/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8379/65536 : ℝ))) 2 (504913864677/1000000000000 : ℝ) (126228466171/250000000000 : ℝ) (497916585821/1000000000000 : ℝ) (497916585829/1000000000000 : ℝ) (501415225249/1000000000000 : ℝ) (501415225257/1000000000000 : ℝ) (50140301917/100000000000 : ℝ) (501403019179/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8379/65536 : ℝ))) 3 (501415225249/1000000000000 : ℝ) (501415225257/1000000000000 : ℝ) (50140301917/100000000000 : ℝ) (501403019179/1000000000000 : ℝ) (501409122209/1000000000000 : ℝ) (250704561109/500000000000 : ℝ) (125352280543/250000000000 : ℝ) (501409122181/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8379/65536 : ℝ))) 4 (501409122209/1000000000000 : ℝ) (250704561109/500000000000 : ℝ) (125352280543/250000000000 : ℝ) (501409122181/1000000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8379/65536 : ℝ))) 5 (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8379/65536 : ℝ))) 6 (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8379/65536 : ℝ))) 7 (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8379/65536 : ℝ)) hmem 8 (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8379/65536 : ℝ))) hcmem 8 (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8379/65536 : ℝ)) (992056841107/1000000000000 : ℝ) (99205684111/100000000000 : ℝ) (50140912219/100000000000 : ℝ) (2507045611/5000000000 : ℝ) (793917822769/1000000000000 : ℝ) (198479455697/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0959_exp_lower
  have heNumeric : (2054901725241/1000000000000 : ℝ)/4 ≤ Real.exp (-85256491082489/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901725241/1000000000000 : ℝ)/4 ≤ Real.exp ((67031/524288 : ℝ)-(198479455697/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67031/524288 : ℝ) (8379/65536 : ℝ) (198479455697/250000000000 : ℝ) (2054901725241/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0960; no trusted numerical premise.
theorem cover8_leaf0960_exp_radius : (998004255075941531/1000000000000000000 : ℝ) ≤ Real.exp ((-67033/4194304 : ℝ)/8) ∧ Real.exp ((-67033/4194304 : ℝ)/8) ≤ (249501063768985383/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67033/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0960_exp_lower : (230028364683502169/250000000000000000 : ℝ) ≤ Real.exp ((-10657061354501/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657061354501/16000000000000 : ℝ)/8) ≤ (920113458734008677/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657061354501/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0960_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450864599/500000000000 : ℝ) ≤ 4*Real.exp (8379/65536 : ℝ)*Real.exp (-mu (radius 8 (67033/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450864599/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67033/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0960_exp_radius
  have hrNumeric : (246036280127/250000000000 : ℝ) ≤ Real.exp (-67033/4194304 : ℝ) ∧ Real.exp (-67033/4194304 : ℝ) ≤ (984145120509/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246036280127/250000000000 : ℝ) ≤ (radius 8 (67033/524288 : ℝ)) ∧ (radius 8 (67033/524288 : ℝ)) ≤ (984145120509/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67033/524288 : ℝ)) (246036280127/250000000000 : ℝ) (984145120509/1000000000000 : ℝ) (177365108683/1000000000000 : ℝ) (17736510869/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67033/524288 : ℝ)) (246036280127/250000000000 : ℝ) (984145120509/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67033/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246036280127/250000000000 : ℝ) (984145120509/1000000000000 : ℝ) (496036280127/500000000000 : ℝ) (198414512051/200000000000 : ℝ) (99204088651/100000000000 : ℝ) (992040886511/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67033/524288 : ℝ)) 1 (496036280127/500000000000 : ℝ) (198414512051/200000000000 : ℝ) (99204088651/100000000000 : ℝ) (992040886511/1000000000000 : ℝ) (496028361691/500000000000 : ℝ) (992056723383/1000000000000 : ℝ) (198411344651/200000000000 : ℝ) (992056723257/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67033/524288 : ℝ)) 2 (496028361691/500000000000 : ℝ) (992056723383/1000000000000 : ℝ) (198411344651/200000000000 : ℝ) (992056723257/1000000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67033/524288 : ℝ)) 3 (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67033/524288 : ℝ)) 4 (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67033/524288 : ℝ)) 5 (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67033/524288 : ℝ)) 6 (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67033/524288 : ℝ)) 7 (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67033/524288 : ℝ))) (177365108683/1000000000000 : ℝ) (17736510869/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67033/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177365108683/1000000000000 : ℝ) (17736510869/100000000000 : ℝ) (588682554341/1000000000000 : ℝ) (117736510869/200000000000 : ℝ) (421147371691/1000000000000 : ℝ) (421147371701/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67033/524288 : ℝ))) 1 (588682554341/1000000000000 : ℝ) (117736510869/200000000000 : ℝ) (421147371691/1000000000000 : ℝ) (421147371701/1000000000000 : ℝ) (63114370377/125000000000 : ℝ) (504914963023/1000000000000 : ℝ) (497917774859/1000000000000 : ℝ) (124479443717/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67033/524288 : ℝ))) 2 (63114370377/125000000000 : ℝ) (504914963023/1000000000000 : ℝ) (497917774859/1000000000000 : ℝ) (124479443717/250000000000 : ℝ) (501416368937/1000000000000 : ℝ) (250708184473/500000000000 : ℝ) (501404163203/1000000000000 : ℝ) (125351040803/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67033/524288 : ℝ))) 3 (501416368937/1000000000000 : ℝ) (250708184473/500000000000 : ℝ) (501404163203/1000000000000 : ℝ) (125351040803/250000000000 : ℝ) (50141026607/100000000000 : ℝ) (501410266079/1000000000000 : ℝ) (31338141627/62500000000 : ℝ) (250705133021/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67033/524288 : ℝ))) 4 (50141026607/100000000000 : ℝ) (501410266079/1000000000000 : ℝ) (31338141627/62500000000 : ℝ) (250705133021/500000000000 : ℝ) (501410266051/1000000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67033/524288 : ℝ))) 5 (501410266051/1000000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67033/524288 : ℝ))) 6 (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67033/524288 : ℝ))) 7 (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67033/524288 : ℝ)) hmem 8 (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67033/524288 : ℝ))) hcmem 8 (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67033/524288 : ℝ)) (496028361659/500000000000 : ℝ) (24801418083/25000000000 : ℝ) (10028205321/20000000000 : ℝ) (501410266061/1000000000000 : ℝ) (793919728191/1000000000000 : ℝ) (793919728211/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0960_exp_lower
  have heNumeric : (1027450864599/500000000000 : ℝ)/4 ≤ Real.exp (-10657061354501/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450864599/500000000000 : ℝ)/4 ≤ Real.exp ((8379/65536 : ℝ)-(793919728211/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8379/65536 : ℝ) (67033/524288 : ℝ) (793919728211/1000000000000 : ℝ) (1027450864599/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0961; no trusted numerical premise.
theorem cover8_leaf0961_exp_radius : (998004225333097421/1000000000000000000 : ℝ) ≤ Real.exp ((-33517/2097152 : ℝ)/8) ∧ Real.exp ((-33517/2097152 : ℝ)/8) ≤ (499002112666548711/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33517/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0961_exp_lower : (184022691791349783/200000000000000000 : ℝ) ≤ Real.exp ((-85256490588119/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256490588119/128000000000000 : ℝ)/8) ≤ (230028364739187229/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256490588119/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0961_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450866589/500000000000 : ℝ) ≤ 4*Real.exp (67033/524288 : ℝ)*Real.exp (-mu (radius 8 (33517/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450866589/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33517/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0961_exp_radius
  have hrNumeric : (984144885869/1000000000000 : ℝ) ≤ Real.exp (-33517/2097152 : ℝ) ∧ Real.exp (-33517/2097152 : ℝ) ≤ (98414488587/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984144885869/1000000000000 : ℝ) ≤ (radius 8 (33517/262144 : ℝ)) ∧ (radius 8 (33517/262144 : ℝ)) ≤ (98414488587/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33517/262144 : ℝ)) (984144885869/1000000000000 : ℝ) (98414488587/100000000000 : ℝ) (177366410619/1000000000000 : ℝ) (283786257/1600000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33517/262144 : ℝ)) (984144885869/1000000000000 : ℝ) (98414488587/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33517/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984144885869/1000000000000 : ℝ) (98414488587/100000000000 : ℝ) (496036221467/500000000000 : ℝ) (198414488587/200000000000 : ℝ) (992040768249/1000000000000 : ℝ) (3968163073/4000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33517/262144 : ℝ)) 1 (496036221467/500000000000 : ℝ) (198414488587/200000000000 : ℝ) (992040768249/1000000000000 : ℝ) (3968163073/4000000000 : ℝ) (992056605591/1000000000000 : ℝ) (992056605593/1000000000000 : ℝ) (198411321093/200000000000 : ℝ) (992056605467/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33517/262144 : ℝ)) 2 (992056605591/1000000000000 : ℝ) (992056605593/1000000000000 : ℝ) (198411321093/200000000000 : ℝ) (992056605467/1000000000000 : ℝ) (124007075691/125000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33517/262144 : ℝ)) 3 (124007075691/125000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33517/262144 : ℝ)) 4 (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33517/262144 : ℝ)) 5 (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33517/262144 : ℝ)) 6 (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33517/262144 : ℝ)) 7 (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33517/262144 : ℝ))) (177366410619/1000000000000 : ℝ) (283786257/1600000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33517/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177366410619/1000000000000 : ℝ) (283786257/1600000000 : ℝ) (588683205309/1000000000000 : ℝ) (588683205313/1000000000000 : ℝ) (42114891739/100000000000 : ℝ) (210574458699/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33517/262144 : ℝ))) 1 (588683205309/1000000000000 : ℝ) (588683205313/1000000000000 : ℝ) (42114891739/100000000000 : ℝ) (210574458699/500000000000 : ℝ) (504916061349/1000000000000 : ℝ) (126229015339/250000000000 : ℝ) (49791896389/100000000000 : ℝ) (497918963897/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33517/262144 : ℝ))) 2 (504916061349/1000000000000 : ℝ) (126229015339/250000000000 : ℝ) (49791896389/100000000000 : ℝ) (497918963897/1000000000000 : ℝ) (501417512619/1000000000000 : ℝ) (501417512627/1000000000000 : ℝ) (501405307229/1000000000000 : ℝ) (501405307237/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33517/262144 : ℝ))) 3 (501417512619/1000000000000 : ℝ) (501417512627/1000000000000 : ℝ) (501405307229/1000000000000 : ℝ) (501405307237/1000000000000 : ℝ) (125352852481/250000000000 : ℝ) (125352852483/250000000000 : ℝ) (250705704943/500000000000 : ℝ) (100282281979/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33517/262144 : ℝ))) 4 (125352852481/250000000000 : ℝ) (125352852483/250000000000 : ℝ) (250705704943/500000000000 : ℝ) (100282281979/200000000000 : ℝ) (100282281981/200000000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33517/262144 : ℝ))) 5 (100282281981/200000000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33517/262144 : ℝ))) 6 (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33517/262144 : ℝ))) 7 (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33517/262144 : ℝ)) hmem 8 (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33517/262144 : ℝ))) hcmem 8 (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33517/262144 : ℝ)) (992056605527/1000000000000 : ℝ) (99205660553/100000000000 : ℝ) (31338213119/62500000000 : ℝ) (250705704957/500000000000 : ℝ) (198480408401/250000000000 : ℝ) (793921633623/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0961_exp_lower
  have heNumeric : (1027450866589/500000000000 : ℝ)/4 ≤ Real.exp (-85256490588119/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450866589/500000000000 : ℝ)/4 ≤ Real.exp ((67033/524288 : ℝ)-(793921633623/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67033/524288 : ℝ) (33517/262144 : ℝ) (793921633623/1000000000000 : ℝ) (1027450866589/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0962; no trusted numerical premise.
theorem cover8_leaf0962_exp_radius : (249501048897563549/250000000000000000 : ℝ) ≤ Real.exp ((-67035/4194304 : ℝ)/8) ∧ Real.exp ((-67035/4194304 : ℝ)/8) ≤ (998004195590254197/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67035/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0962_exp_lower : (920113459182479523/1000000000000000000 : ℝ) ≤ Real.exp ((-42628245168451/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628245168451/64000000000000 : ℝ)/8) ≤ (230028364795619881/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628245168451/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0962_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901737211/1000000000000 : ℝ) ≤ 4*Real.exp (33517/262144 : ℝ)*Real.exp (-mu (radius 8 (67035/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901737211/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67035/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0962_exp_radius
  have hrNumeric : (984144651231/1000000000000 : ℝ) ≤ Real.exp (-67035/4194304 : ℝ) ∧ Real.exp (-67035/4194304 : ℝ) ≤ (30754520351/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984144651231/1000000000000 : ℝ) ≤ (radius 8 (67035/524288 : ℝ)) ∧ (radius 8 (67035/524288 : ℝ)) ≤ (30754520351/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67035/524288 : ℝ)) (984144651231/1000000000000 : ℝ) (30754520351/31250000000 : ℝ) (177367712539/1000000000000 : ℝ) (35473542509/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67035/524288 : ℝ)) (984144651231/1000000000000 : ℝ) (30754520351/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67035/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984144651231/1000000000000 : ℝ) (30754520351/31250000000 : ℝ) (198414465123/200000000000 : ℝ) (62004520351/62500000000 : ℝ) (992040649989/1000000000000 : ℝ) (99204064999/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67035/524288 : ℝ)) 1 (198414465123/200000000000 : ℝ) (62004520351/62500000000 : ℝ) (992040649989/1000000000000 : ℝ) (99204064999/100000000000 : ℝ) (496028243901/500000000000 : ℝ) (992056487803/1000000000000 : ℝ) (39682259507/40000000000 : ℝ) (992056487677/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67035/524288 : ℝ)) 2 (496028243901/500000000000 : ℝ) (992056487803/1000000000000 : ℝ) (39682259507/40000000000 : ℝ) (992056487677/1000000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67035/524288 : ℝ)) 3 (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67035/524288 : ℝ)) 4 (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67035/524288 : ℝ)) 5 (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67035/524288 : ℝ)) 6 (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67035/524288 : ℝ)) 7 (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67035/524288 : ℝ))) (177367712539/1000000000000 : ℝ) (35473542509/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67035/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177367712539/1000000000000 : ℝ) (35473542509/200000000000 : ℝ) (588683856269/1000000000000 : ℝ) (588683856273/1000000000000 : ℝ) (421150463063/1000000000000 : ℝ) (13160951971/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67035/524288 : ℝ))) 1 (588683856269/1000000000000 : ℝ) (588683856273/1000000000000 : ℝ) (421150463063/1000000000000 : ℝ) (13160951971/31250000000 : ℝ) (252458579833/500000000000 : ℝ) (504917159673/1000000000000 : ℝ) (497920152901/1000000000000 : ℝ) (497920152909/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67035/524288 : ℝ))) 2 (252458579833/500000000000 : ℝ) (504917159673/1000000000000 : ℝ) (497920152901/1000000000000 : ℝ) (497920152909/1000000000000 : ℝ) (501418656283/1000000000000 : ℝ) (501418656291/1000000000000 : ℝ) (250703225619/500000000000 : ℝ) (250703225623/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67035/524288 : ℝ))) 3 (501418656283/1000000000000 : ℝ) (501418656291/1000000000000 : ℝ) (250703225619/500000000000 : ℝ) (250703225623/500000000000 : ℝ) (3133828461/6250000000 : ℝ) (501412553769/1000000000000 : ℝ) (501412553723/1000000000000 : ℝ) (125353138433/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67035/524288 : ℝ))) 4 (3133828461/6250000000 : ℝ) (501412553769/1000000000000 : ℝ) (501412553723/1000000000000 : ℝ) (125353138433/250000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67035/524288 : ℝ))) 5 (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67035/524288 : ℝ))) 6 (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67035/524288 : ℝ))) 7 (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67035/524288 : ℝ)) hmem 8 (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67035/524288 : ℝ))) hcmem 8 (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67035/524288 : ℝ)) (496028243869/500000000000 : ℝ) (49602824387/50000000000 : ℝ) (501412553741/1000000000000 : ℝ) (501412553751/1000000000000 : ℝ) (79392353899/100000000000 : ℝ) (793923539009/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0962_exp_lower
  have heNumeric : (2054901737211/1000000000000 : ℝ)/4 ≤ Real.exp (-42628245168451/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901737211/1000000000000 : ℝ)/4 ≤ Real.exp ((33517/262144 : ℝ)-(793923539009/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33517/262144 : ℝ) (67035/524288 : ℝ) (793923539009/1000000000000 : ℝ) (2054901737211/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0963; no trusted numerical premise.
theorem cover8_leaf0963_exp_radius : (499002082923705929/500000000000000000 : ℝ) ≤ Real.exp ((-16759/1048576 : ℝ)/8) ∧ Real.exp ((-16759/1048576 : ℝ)/8) ≤ (998004165847411859/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16759/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0963_exp_lower : (460056729704795151/500000000000000000 : ℝ) ≤ Real.exp ((-85256490084149/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256490084149/128000000000000 : ℝ)/8) ≤ (920113459409590303/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256490084149/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0963_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901741269/1000000000000 : ℝ) ≤ 4*Real.exp (67035/524288 : ℝ)*Real.exp (-mu (radius 8 (16759/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901741269/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16759/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0963_exp_radius
  have hrNumeric : (61509026037/62500000000 : ℝ) ≤ Real.exp (-16759/1048576 : ℝ) ∧ Real.exp (-16759/1048576 : ℝ) ≤ (984144416593/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61509026037/62500000000 : ℝ) ≤ (radius 8 (16759/131072 : ℝ)) ∧ (radius 8 (16759/131072 : ℝ)) ≤ (984144416593/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16759/131072 : ℝ)) (61509026037/62500000000 : ℝ) (984144416593/1000000000000 : ℝ) (35473802891/200000000000 : ℝ) (177369014461/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16759/131072 : ℝ)) (61509026037/62500000000 : ℝ) (984144416593/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16759/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61509026037/62500000000 : ℝ) (984144416593/1000000000000 : ℝ) (124009026037/125000000000 : ℝ) (992072208297/1000000000000 : ℝ) (62002533233/62500000000 : ℝ) (992040531729/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16759/131072 : ℝ)) 1 (124009026037/125000000000 : ℝ) (992072208297/1000000000000 : ℝ) (62002533233/62500000000 : ℝ) (992040531729/1000000000000 : ℝ) (248014092503/250000000000 : ℝ) (992056370013/1000000000000 : ℝ) (198411273977/200000000000 : ℝ) (992056369887/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16759/131072 : ℝ)) 2 (248014092503/250000000000 : ℝ) (992056370013/1000000000000 : ℝ) (198411273977/200000000000 : ℝ) (992056369887/1000000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16759/131072 : ℝ)) 3 (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16759/131072 : ℝ)) 4 (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16759/131072 : ℝ)) 5 (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16759/131072 : ℝ)) 6 (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16759/131072 : ℝ)) 7 (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16759/131072 : ℝ))) (35473802891/200000000000 : ℝ) (177369014461/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16759/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35473802891/200000000000 : ℝ) (177369014461/1000000000000 : ℝ) (588684507227/1000000000000 : ℝ) (588684507231/1000000000000 : ℝ) (421152008727/1000000000000 : ℝ) (84230401747/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16759/131072 : ℝ))) 1 (588684507227/1000000000000 : ℝ) (588684507231/1000000000000 : ℝ) (421152008727/1000000000000 : ℝ) (84230401747/200000000000 : ℝ) (504918257977/1000000000000 : ℝ) (504918257983/1000000000000 : ℝ) (99584268381/200000000000 : ℝ) (497921341913/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16759/131072 : ℝ))) 2 (504918257977/1000000000000 : ℝ) (504918257983/1000000000000 : ℝ) (99584268381/200000000000 : ℝ) (497921341913/1000000000000 : ℝ) (501419799941/1000000000000 : ℝ) (125354949987/250000000000 : ℝ) (501407595239/1000000000000 : ℝ) (501407595247/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16759/131072 : ℝ))) 3 (501419799941/1000000000000 : ℝ) (125354949987/250000000000 : ℝ) (501407595239/1000000000000 : ℝ) (501407595247/1000000000000 : ℝ) (50141369759/100000000000 : ℝ) (250706848799/500000000000 : ℝ) (31338356097/62500000000 : ℝ) (501413697561/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16759/131072 : ℝ))) 4 (50141369759/100000000000 : ℝ) (250706848799/500000000000 : ℝ) (31338356097/62500000000 : ℝ) (501413697561/1000000000000 : ℝ) (501413697571/1000000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16759/131072 : ℝ))) 5 (501413697571/1000000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16759/131072 : ℝ))) 6 (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16759/131072 : ℝ))) 7 (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16759/131072 : ℝ)) hmem 8 (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16759/131072 : ℝ))) hcmem 8 (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16759/131072 : ℝ)) (248014092487/250000000000 : ℝ) (19841127399/20000000000 : ℝ) (50141369757/100000000000 : ℝ) (25070684879/50000000000 : ℝ) (198481361091/250000000000 : ℝ) (793925444383/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0963_exp_lower
  have heNumeric : (2054901741269/1000000000000 : ℝ)/4 ≤ Real.exp (-85256490084149/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901741269/1000000000000 : ℝ)/4 ≤ Real.exp ((67035/524288 : ℝ)-(793925444383/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67035/524288 : ℝ) (16759/131072 : ℝ) (793925444383/1000000000000 : ℝ) (2054901741269/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0964; no trusted numerical premise.
theorem cover8_leaf0964_exp_radius : (499002068052285203/500000000000000000 : ℝ) ≤ Real.exp ((-67037/4194304 : ℝ)/8) ∧ Real.exp ((-67037/4194304 : ℝ)/8) ≤ (998004136104570407/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67037/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0964_exp_lower : (920113459639691449/1000000000000000000 : ℝ) ≤ Real.exp ((-21314122457017/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314122457017/32000000000000 : ℝ)/8) ≤ (18402269192793829/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314122457017/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0964_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745087269/50000000000 : ℝ) ≤ 4*Real.exp (16759/131072 : ℝ)*Real.exp (-mu (radius 8 (67037/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (102745087269/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67037/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0964_exp_radius
  have hrNumeric : (492072090977/500000000000 : ℝ) ≤ Real.exp (-67037/4194304 : ℝ) ∧ Real.exp (-67037/4194304 : ℝ) ≤ (196828836391/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492072090977/500000000000 : ℝ) ≤ (radius 8 (67037/524288 : ℝ)) ∧ (radius 8 (67037/524288 : ℝ)) ≤ (196828836391/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67037/524288 : ℝ)) (492072090977/500000000000 : ℝ) (196828836391/200000000000 : ℝ) (35474063271/200000000000 : ℝ) (88685158181/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67037/524288 : ℝ)) (492072090977/500000000000 : ℝ) (196828836391/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67037/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492072090977/500000000000 : ℝ) (196828836391/200000000000 : ℝ) (992072090977/1000000000000 : ℝ) (496036045489/500000000000 : ℝ) (248010103367/250000000000 : ℝ) (992040413469/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67037/524288 : ℝ)) 1 (992072090977/1000000000000 : ℝ) (496036045489/500000000000 : ℝ) (248010103367/250000000000 : ℝ) (992040413469/1000000000000 : ℝ) (496028126111/500000000000 : ℝ) (15500878941/15625000000 : ℝ) (15500878939/15625000000 : ℝ) (496028126049/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67037/524288 : ℝ)) 2 (496028126111/500000000000 : ℝ) (15500878941/15625000000 : ℝ) (15500878939/15625000000 : ℝ) (496028126049/500000000000 : ℝ) (992056252159/1000000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67037/524288 : ℝ)) 3 (992056252159/1000000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67037/524288 : ℝ)) 4 (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67037/524288 : ℝ)) 5 (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67037/524288 : ℝ)) 6 (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67037/524288 : ℝ)) 7 (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67037/524288 : ℝ))) (35474063271/200000000000 : ℝ) (88685158181/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67037/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35474063271/200000000000 : ℝ) (88685158181/500000000000 : ℝ) (588685158177/1000000000000 : ℝ) (588685158181/1000000000000 : ℝ) (84230710873/200000000000 : ℝ) (673845687/1600000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67037/524288 : ℝ))) 1 (588685158177/1000000000000 : ℝ) (588685158181/1000000000000 : ℝ) (84230710873/200000000000 : ℝ) (673845687/1600000000 : ℝ) (504919356271/1000000000000 : ℝ) (252459678139/500000000000 : ℝ) (49792253089/100000000000 : ℝ) (248961265449/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67037/524288 : ℝ))) 2 (504919356271/1000000000000 : ℝ) (252459678139/500000000000 : ℝ) (49792253089/100000000000 : ℝ) (248961265449/500000000000 : ℝ) (25071047179/50000000000 : ℝ) (125355235897/250000000000 : ℝ) (501408739223/1000000000000 : ℝ) (15669023101/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67037/524288 : ℝ))) 3 (25071047179/50000000000 : ℝ) (125355235897/250000000000 : ℝ) (501408739223/1000000000000 : ℝ) (15669023101/31250000000 : ℝ) (501414841401/1000000000000 : ℝ) (50141484141/100000000000 : ℝ) (125353710341/250000000000 : ℝ) (501414841373/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67037/524288 : ℝ))) 4 (501414841401/1000000000000 : ℝ) (50141484141/100000000000 : ℝ) (125353710341/250000000000 : ℝ) (501414841373/1000000000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67037/524288 : ℝ))) 5 (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67037/524288 : ℝ))) 6 (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67037/524288 : ℝ))) 7 (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67037/524288 : ℝ)) hmem 8 (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67037/524288 : ℝ))) hcmem 8 (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67037/524288 : ℝ)) (496028126079/500000000000 : ℝ) (992056252161/1000000000000 : ℝ) (250707420691/500000000000 : ℝ) (31338427587/62500000000 : ℝ) (793927349711/1000000000000 : ℝ) (793927349731/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0964_exp_lower
  have heNumeric : (102745087269/50000000000 : ℝ)/4 ≤ Real.exp (-21314122457017/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745087269/50000000000 : ℝ)/4 ≤ Real.exp ((16759/131072 : ℝ)-(793927349731/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16759/131072 : ℝ) (67037/524288 : ℝ) (793927349731/1000000000000 : ℝ) (102745087269/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0965; no trusted numerical premise.
theorem cover8_leaf0965_exp_radius : (998004106361729841/1000000000000000000 : ℝ) ≤ Real.exp ((-33519/2097152 : ℝ)/8) ∧ Real.exp ((-33519/2097152 : ℝ)/8) ≤ (499002053180864921/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33519/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0965_exp_lower : (460056729935988933/500000000000000000 : ℝ) ≤ Real.exp ((-17051297913911/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051297913911/25600000000000 : ℝ)/8) ≤ (920113459871977867/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051297913911/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0965_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490174953/100000000000 : ℝ) ≤ 4*Real.exp (67037/524288 : ℝ)*Real.exp (-mu (radius 8 (33519/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490174953/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33519/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0965_exp_radius
  have hrNumeric : (246035986829/250000000000 : ℝ) ≤ Real.exp (-33519/2097152 : ℝ) ∧ Real.exp (-33519/2097152 : ℝ) ≤ (984143947317/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246035986829/250000000000 : ℝ) ≤ (radius 8 (33519/262144 : ℝ)) ∧ (radius 8 (33519/262144 : ℝ)) ≤ (984143947317/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33519/262144 : ℝ)) (246035986829/250000000000 : ℝ) (984143947317/1000000000000 : ℝ) (88685809123/500000000000 : ℝ) (44342904563/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33519/262144 : ℝ)) (246035986829/250000000000 : ℝ) (984143947317/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33519/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246035986829/250000000000 : ℝ) (984143947317/1000000000000 : ℝ) (496035986829/500000000000 : ℝ) (992071973659/1000000000000 : ℝ) (992040295207/1000000000000 : ℝ) (992040295209/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33519/262144 : ℝ)) 1 (496035986829/500000000000 : ℝ) (992071973659/1000000000000 : ℝ) (992040295207/1000000000000 : ℝ) (992040295209/1000000000000 : ℝ) (31001754201/31250000000 : ℝ) (496028067217/500000000000 : ℝ) (496028067153/500000000000 : ℝ) (248014033577/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33519/262144 : ℝ)) 2 (31001754201/31250000000 : ℝ) (496028067217/500000000000 : ℝ) (496028067153/500000000000 : ℝ) (248014033577/250000000000 : ℝ) (992056134369/1000000000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33519/262144 : ℝ)) 3 (992056134369/1000000000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33519/262144 : ℝ)) 4 (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33519/262144 : ℝ)) 5 (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33519/262144 : ℝ)) 6 (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33519/262144 : ℝ)) 7 (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33519/262144 : ℝ))) (88685809123/500000000000 : ℝ) (44342904563/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33519/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88685809123/500000000000 : ℝ) (44342904563/250000000000 : ℝ) (588685809123/1000000000000 : ℝ) (294342904563/500000000000 : ℝ) (105288774997/250000000000 : ℝ) (105288774999/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33519/262144 : ℝ))) 1 (588685809123/1000000000000 : ℝ) (294342904563/500000000000 : ℝ) (105288774997/250000000000 : ℝ) (105288774999/250000000000 : ℝ) (100984090911/200000000000 : ℝ) (504920454561/1000000000000 : ℝ) (497923719863/1000000000000 : ℝ) (49792371987/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33519/262144 : ℝ))) 2 (100984090911/200000000000 : ℝ) (504920454561/1000000000000 : ℝ) (497923719863/1000000000000 : ℝ) (49792371987/100000000000 : ℝ) (501422087209/1000000000000 : ℝ) (31338880451/62500000000 : ℝ) (125352470799/250000000000 : ℝ) (501409883203/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33519/262144 : ℝ))) 3 (501422087209/1000000000000 : ℝ) (31338880451/62500000000 : ℝ) (125352470799/250000000000 : ℝ) (501409883203/1000000000000 : ℝ) (250707992601/500000000000 : ℝ) (50141598521/100000000000 : ℝ) (100283197033/200000000000 : ℝ) (501415985173/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33519/262144 : ℝ))) 4 (250707992601/500000000000 : ℝ) (50141598521/100000000000 : ℝ) (100283197033/200000000000 : ℝ) (501415985173/1000000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33519/262144 : ℝ))) 5 (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33519/262144 : ℝ))) 6 (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33519/262144 : ℝ))) 7 (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33519/262144 : ℝ)) hmem 8 (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33519/262144 : ℝ))) hcmem 8 (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33519/262144 : ℝ)) (31001754199/31250000000 : ℝ) (992056134371/1000000000000 : ℝ) (501415985183/1000000000000 : ℝ) (62676998149/125000000000 : ℝ) (396964627521/500000000000 : ℝ) (39696462753/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0965_exp_lower
  have heNumeric : (205490174953/100000000000 : ℝ)/4 ≤ Real.exp (-17051297913911/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490174953/100000000000 : ℝ)/4 ≤ Real.exp ((67037/524288 : ℝ)-(39696462753/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67037/524288 : ℝ) (33519/262144 : ℝ) (39696462753/50000000000 : ℝ) (205490174953/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0966; no trusted numerical premise.
theorem cover8_leaf0966_exp_radius : (499002038309445081/500000000000000000 : ℝ) ≤ Real.exp ((-67039/4194304 : ℝ)/8) ∧ Real.exp ((-67039/4194304 : ℝ)/8) ≤ (998004076618890163/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67039/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0966_exp_lower : (57507091256653097/62500000000000000 : ℝ) ≤ Real.exp ((-8525648930861/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525648930861/12800000000000 : ℝ)/8) ≤ (920113460106449553/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525648930861/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0966_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901753719/1000000000000 : ℝ) ≤ 4*Real.exp (33519/262144 : ℝ)*Real.exp (-mu (radius 8 (67039/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901753719/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67039/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0966_exp_radius
  have hrNumeric : (492071856339/500000000000 : ℝ) ≤ Real.exp (-67039/4194304 : ℝ) ∧ Real.exp (-67039/4194304 : ℝ) ≤ (984143712679/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492071856339/500000000000 : ℝ) ≤ (radius 8 (67039/524288 : ℝ)) ∧ (radius 8 (67039/524288 : ℝ)) ≤ (984143712679/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67039/524288 : ℝ)) (492071856339/500000000000 : ℝ) (984143712679/1000000000000 : ℝ) (177372920127/1000000000000 : ℝ) (177372920133/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67039/524288 : ℝ)) (492071856339/500000000000 : ℝ) (984143712679/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67039/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492071856339/500000000000 : ℝ) (984143712679/1000000000000 : ℝ) (992071856339/1000000000000 : ℝ) (49603592817/50000000000 : ℝ) (992040176947/1000000000000 : ℝ) (248010044237/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67039/524288 : ℝ)) 1 (992071856339/1000000000000 : ℝ) (49603592817/50000000000 : ℝ) (992040176947/1000000000000 : ℝ) (248010044237/250000000000 : ℝ) (992056016643/1000000000000 : ℝ) (248014004161/250000000000 : ℝ) (248014004129/250000000000 : ℝ) (496028008259/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67039/524288 : ℝ)) 2 (992056016643/1000000000000 : ℝ) (248014004161/250000000000 : ℝ) (248014004129/250000000000 : ℝ) (496028008259/500000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67039/524288 : ℝ)) 3 (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67039/524288 : ℝ)) 4 (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67039/524288 : ℝ)) 5 (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67039/524288 : ℝ)) 6 (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67039/524288 : ℝ)) 7 (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67039/524288 : ℝ))) (177372920127/1000000000000 : ℝ) (177372920133/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67039/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177372920127/1000000000000 : ℝ) (177372920133/1000000000000 : ℝ) (588686460063/1000000000000 : ℝ) (588686460067/1000000000000 : ℝ) (52644580699/125000000000 : ℝ) (526445807/1250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67039/524288 : ℝ))) 1 (588686460063/1000000000000 : ℝ) (588686460067/1000000000000 : ℝ) (52644580699/125000000000 : ℝ) (526445807/1250000000 : ℝ) (504921552827/1000000000000 : ℝ) (252460776417/500000000000 : ℝ) (248962454411/500000000000 : ℝ) (497924908829/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67039/524288 : ℝ))) 2 (504921552827/1000000000000 : ℝ) (252460776417/500000000000 : ℝ) (248962454411/500000000000 : ℝ) (497924908829/1000000000000 : ℝ) (62677903853/125000000000 : ℝ) (31338951927/62500000000 : ℝ) (125352756789/250000000000 : ℝ) (125352756791/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67039/524288 : ℝ))) 3 (62677903853/125000000000 : ℝ) (31338951927/62500000000 : ℝ) (125352756789/250000000000 : ℝ) (125352756791/250000000000 : ℝ) (50141712899/100000000000 : ℝ) (250708564499/500000000000 : ℝ) (62677141119/125000000000 : ℝ) (501417128961/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67039/524288 : ℝ))) 4 (50141712899/100000000000 : ℝ) (250708564499/500000000000 : ℝ) (62677141119/125000000000 : ℝ) (501417128961/1000000000000 : ℝ) (501417128971/1000000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67039/524288 : ℝ))) 5 (501417128971/1000000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67039/524288 : ℝ))) 6 (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67039/524288 : ℝ))) 7 (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67039/524288 : ℝ)) hmem 8 (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67039/524288 : ℝ))) hcmem 8 (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67039/524288 : ℝ)) (992056016579/1000000000000 : ℝ) (992056016581/1000000000000 : ℝ) (50141712897/100000000000 : ℝ) (25070856449/50000000000 : ℝ) (793931160351/1000000000000 : ℝ) (79393116037/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0966_exp_lower
  have heNumeric : (2054901753719/1000000000000 : ℝ)/4 ≤ Real.exp (-8525648930861/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901753719/1000000000000 : ℝ)/4 ≤ Real.exp ((33519/262144 : ℝ)-(79393116037/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33519/262144 : ℝ) (67039/524288 : ℝ) (79393116037/100000000000 : ℝ) (2054901753719/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0967; no trusted numerical premise.
theorem cover8_leaf0967_exp_radius : (99800404687605137/100000000000000000 : ℝ) ≤ Real.exp ((-2095/131072 : ℝ)/8) ∧ Real.exp ((-2095/131072 : ℝ)/8) ≤ (998004046876051371/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2095/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0967_exp_lower : (460056730171610761/500000000000000000 : ℝ) ≤ Real.exp ((-17051297809021/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051297809021/25600000000000 : ℝ)/8) ≤ (920113460343221523/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051297809021/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0967_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901757949/1000000000000 : ℝ) ≤ 4*Real.exp (67039/524288 : ℝ)*Real.exp (-mu (radius 8 (2095/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901757949/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2095/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0967_exp_radius
  have hrNumeric : (24603586951/25000000000 : ℝ) ≤ Real.exp (-2095/131072 : ℝ) ∧ Real.exp (-2095/131072 : ℝ) ≤ (984143478041/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24603586951/25000000000 : ℝ) ≤ (radius 8 (2095/16384 : ℝ)) ∧ (radius 8 (2095/16384 : ℝ)) ≤ (984143478041/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2095/16384 : ℝ)) (24603586951/25000000000 : ℝ) (984143478041/1000000000000 : ℝ) (177374221997/1000000000000 : ℝ) (44343555501/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2095/16384 : ℝ)) (24603586951/25000000000 : ℝ) (984143478041/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2095/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24603586951/25000000000 : ℝ) (984143478041/1000000000000 : ℝ) (49603586951/50000000000 : ℝ) (992071739021/1000000000000 : ℝ) (992040058687/1000000000000 : ℝ) (15500625917/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2095/16384 : ℝ)) 1 (49603586951/50000000000 : ℝ) (992071739021/1000000000000 : ℝ) (992040058687/1000000000000 : ℝ) (15500625917/15625000000 : ℝ) (992055898853/1000000000000 : ℝ) (198411179771/200000000000 : ℝ) (992055898727/1000000000000 : ℝ) (992055898729/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2095/16384 : ℝ)) 2 (992055898853/1000000000000 : ℝ) (198411179771/200000000000 : ℝ) (992055898727/1000000000000 : ℝ) (992055898729/1000000000000 : ℝ) (99205589879/100000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2095/16384 : ℝ)) 3 (99205589879/100000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2095/16384 : ℝ)) 4 (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2095/16384 : ℝ)) 5 (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2095/16384 : ℝ)) 6 (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2095/16384 : ℝ)) 7 (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2095/16384 : ℝ))) (177374221997/1000000000000 : ℝ) (44343555501/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2095/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177374221997/1000000000000 : ℝ) (44343555501/250000000000 : ℝ) (294343555499/500000000000 : ℝ) (294343555501/500000000000 : ℝ) (210579095589/500000000000 : ℝ) (105289547797/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2095/16384 : ℝ))) 1 (294343555499/500000000000 : ℝ) (294343555501/500000000000 : ℝ) (210579095589/500000000000 : ℝ) (105289547797/250000000000 : ℝ) (31557665693/62500000000 : ℝ) (100984530219/200000000000 : ℝ) (497926097767/1000000000000 : ℝ) (19917043911/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2095/16384 : ℝ))) 2 (31557665693/62500000000 : ℝ) (100984530219/200000000000 : ℝ) (497926097767/1000000000000 : ℝ) (19917043911/40000000000 : ℝ) (501424374427/1000000000000 : ℝ) (100284874887/200000000000 : ℝ) (501412171103/1000000000000 : ℝ) (501412171111/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2095/16384 : ℝ))) 3 (501424374427/1000000000000 : ℝ) (100284874887/200000000000 : ℝ) (501412171103/1000000000000 : ℝ) (501412171111/1000000000000 : ℝ) (100283654553/200000000000 : ℝ) (501418272773/1000000000000 : ℝ) (501418272727/1000000000000 : ℝ) (15669321023/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2095/16384 : ℝ))) 4 (100283654553/200000000000 : ℝ) (501418272773/1000000000000 : ℝ) (501418272727/1000000000000 : ℝ) (15669321023/31250000000 : ℝ) (250709136373/500000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2095/16384 : ℝ))) 5 (250709136373/500000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2095/16384 : ℝ))) 6 (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2095/16384 : ℝ))) 7 (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2095/16384 : ℝ)) hmem 8 (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2095/16384 : ℝ))) hcmem 8 (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2095/16384 : ℝ)) (992055898789/1000000000000 : ℝ) (124006987349/125000000000 : ℝ) (100283654549/200000000000 : ℝ) (100283654551/200000000000 : ℝ) (793933065641/1000000000000 : ℝ) (39696653283/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0967_exp_lower
  have heNumeric : (2054901757949/1000000000000 : ℝ)/4 ≤ Real.exp (-17051297809021/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901757949/1000000000000 : ℝ)/4 ≤ Real.exp ((67039/524288 : ℝ)-(39696653283/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67039/524288 : ℝ) (2095/16384 : ℝ) (39696653283/50000000000 : ℝ) (2054901757949/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0968; no trusted numerical premise.
theorem cover8_leaf0968_exp_radius : (124750502141651683/125000000000000000 : ℝ) ≤ Real.exp ((-67041/4194304 : ℝ)/8) ∧ Real.exp ((-67041/4194304 : ℝ)/8) ≤ (199600803426642693/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67041/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0968_exp_lower : (460056730290456803/500000000000000000 : ℝ) ≤ Real.exp ((-2664265274393/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664265274393/4000000000000 : ℝ)/8) ≤ (920113460580913607/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664265274393/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0968_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725440549/250000000000 : ℝ) ≤ 4*Real.exp (2095/16384 : ℝ)*Real.exp (-mu (radius 8 (67041/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725440549/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67041/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0968_exp_radius
  have hrNumeric : (984143243401/1000000000000 : ℝ) ≤ Real.exp (-67041/4194304 : ℝ) ∧ Real.exp (-67041/4194304 : ℝ) ≤ (492071621701/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984143243401/1000000000000 : ℝ) ≤ (radius 8 (67041/524288 : ℝ)) ∧ (radius 8 (67041/524288 : ℝ)) ≤ (492071621701/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67041/524288 : ℝ)) (984143243401/1000000000000 : ℝ) (492071621701/500000000000 : ℝ) (22171940483/125000000000 : ℝ) (177375523871/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67041/524288 : ℝ)) (984143243401/1000000000000 : ℝ) (492071621701/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67041/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984143243401/1000000000000 : ℝ) (492071621701/500000000000 : ℝ) (9920716217/10000000000 : ℝ) (992071621701/1000000000000 : ℝ) (496019970213/500000000000 : ℝ) (992039940427/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67041/524288 : ℝ)) 1 (9920716217/10000000000 : ℝ) (992071621701/1000000000000 : ℝ) (496019970213/500000000000 : ℝ) (992039940427/1000000000000 : ℝ) (992055781063/1000000000000 : ℝ) (124006972633/125000000000 : ℝ) (124006972617/125000000000 : ℝ) (496027890469/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67041/524288 : ℝ)) 2 (992055781063/1000000000000 : ℝ) (124006972633/125000000000 : ℝ) (124006972617/125000000000 : ℝ) (496027890469/500000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67041/524288 : ℝ)) 3 (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67041/524288 : ℝ)) 4 (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67041/524288 : ℝ)) 5 (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67041/524288 : ℝ)) 6 (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67041/524288 : ℝ)) 7 (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67041/524288 : ℝ))) (22171940483/125000000000 : ℝ) (177375523871/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67041/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22171940483/125000000000 : ℝ) (177375523871/1000000000000 : ℝ) (147171940483/250000000000 : ℝ) (36792985121/62500000000 : ℝ) (84231947351/200000000000 : ℝ) (105289934191/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67041/524288 : ℝ))) 1 (147171940483/250000000000 : ℝ) (36792985121/62500000000 : ℝ) (84231947351/200000000000 : ℝ) (105289934191/250000000000 : ℝ) (504923749343/1000000000000 : ℝ) (10098474987/20000000000 : ℝ) (99585457341/200000000000 : ℝ) (497927286713/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67041/524288 : ℝ))) 2 (504923749343/1000000000000 : ℝ) (10098474987/20000000000 : ℝ) (99585457341/200000000000 : ℝ) (497927286713/1000000000000 : ℝ) (62678189753/125000000000 : ℝ) (31339094877/62500000000 : ℝ) (501413315043/1000000000000 : ℝ) (125353328763/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67041/524288 : ℝ))) 3 (62678189753/125000000000 : ℝ) (31339094877/62500000000 : ℝ) (501413315043/1000000000000 : ℝ) (125353328763/250000000000 : ℝ) (501419416533/1000000000000 : ℝ) (250709708271/500000000000 : ℝ) (31338713531/62500000000 : ℝ) (100283883301/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67041/524288 : ℝ))) 4 (501419416533/1000000000000 : ℝ) (250709708271/500000000000 : ℝ) (31338713531/62500000000 : ℝ) (100283883301/200000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67041/524288 : ℝ))) 5 (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67041/524288 : ℝ))) 6 (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67041/524288 : ℝ))) 7 (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67041/524288 : ℝ)) hmem 8 (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67041/524288 : ℝ))) hcmem 8 (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67041/524288 : ℝ)) (992055780999/1000000000000 : ℝ) (992055781001/1000000000000 : ℝ) (250709708257/500000000000 : ℝ) (125354854131/250000000000 : ℝ) (793934970923/1000000000000 : ℝ) (396967485471/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0968_exp_lower
  have heNumeric : (513725440549/250000000000 : ℝ)/4 ≤ Real.exp (-2664265274393/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725440549/250000000000 : ℝ)/4 ≤ Real.exp ((2095/16384 : ℝ)-(396967485471/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2095/16384 : ℝ) (67041/524288 : ℝ) (396967485471/500000000000 : ℝ) (513725440549/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0969; no trusted numerical premise.
theorem cover8_leaf0969_exp_radius : (249500996847594111/250000000000000000 : ℝ) ≤ Real.exp ((-33521/2097152 : ℝ)/8) ∧ Real.exp ((-33521/2097152 : ℝ)/8) ≤ (199600797478075289/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33521/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0969_exp_lower : (920113460821941101/1000000000000000000 : ℝ) ≤ Real.exp ((-17051297702467/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051297702467/25600000000000 : ℝ)/8) ≤ (460056730410970551/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051297702467/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0969_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450883251/500000000000 : ℝ) ≤ 4*Real.exp (67041/524288 : ℝ)*Real.exp (-mu (radius 8 (33521/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450883251/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33521/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0969_exp_radius
  have hrNumeric : (984143008763/1000000000000 : ℝ) ≤ Real.exp (-33521/2097152 : ℝ) ∧ Real.exp (-33521/2097152 : ℝ) ≤ (246035752191/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984143008763/1000000000000 : ℝ) ≤ (radius 8 (33521/262144 : ℝ)) ∧ (radius 8 (33521/262144 : ℝ)) ≤ (246035752191/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33521/262144 : ℝ)) (984143008763/1000000000000 : ℝ) (246035752191/250000000000 : ℝ) (35475365143/200000000000 : ℝ) (88688412861/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33521/262144 : ℝ)) (984143008763/1000000000000 : ℝ) (246035752191/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33521/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984143008763/1000000000000 : ℝ) (246035752191/250000000000 : ℝ) (992071504381/1000000000000 : ℝ) (496035752191/500000000000 : ℝ) (198407964433/200000000000 : ℝ) (992039822167/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33521/262144 : ℝ)) 1 (992071504381/1000000000000 : ℝ) (496035752191/500000000000 : ℝ) (198407964433/200000000000 : ℝ) (992039822167/1000000000000 : ℝ) (992055663273/1000000000000 : ℝ) (39682226531/40000000000 : ℝ) (496027831573/500000000000 : ℝ) (992055663149/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33521/262144 : ℝ)) 2 (992055663273/1000000000000 : ℝ) (39682226531/40000000000 : ℝ) (496027831573/500000000000 : ℝ) (992055663149/1000000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33521/262144 : ℝ)) 3 (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33521/262144 : ℝ)) 4 (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33521/262144 : ℝ)) 5 (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33521/262144 : ℝ)) 6 (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33521/262144 : ℝ)) 7 (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33521/262144 : ℝ))) (35475365143/200000000000 : ℝ) (88688412861/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33521/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35475365143/200000000000 : ℝ) (88688412861/500000000000 : ℝ) (588688412857/1000000000000 : ℝ) (588688412861/1000000000000 : ℝ) (421161282307/1000000000000 : ℝ) (105290320579/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33521/262144 : ℝ))) 1 (588688412857/1000000000000 : ℝ) (588688412861/1000000000000 : ℝ) (421161282307/1000000000000 : ℝ) (105290320579/250000000000 : ℝ) (252462423791/500000000000 : ℝ) (504924847589/1000000000000 : ℝ) (62241059453/125000000000 : ℝ) (31120529727/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33521/262144 : ℝ))) 2 (252462423791/500000000000 : ℝ) (504924847589/1000000000000 : ℝ) (62241059453/125000000000 : ℝ) (31120529727/62500000000 : ℝ) (501426661603/1000000000000 : ℝ) (501426661611/1000000000000 : ℝ) (501414458967/1000000000000 : ℝ) (20056578359/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33521/262144 : ℝ))) 3 (501426661603/1000000000000 : ℝ) (501426661611/1000000000000 : ℝ) (501414458967/1000000000000 : ℝ) (20056578359/40000000000 : ℝ) (100284112057/200000000000 : ℝ) (501420560293/1000000000000 : ℝ) (501420560247/1000000000000 : ℝ) (3917348127/7812500000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33521/262144 : ℝ))) 4 (100284112057/200000000000 : ℝ) (501420560293/1000000000000 : ℝ) (501420560247/1000000000000 : ℝ) (3917348127/7812500000 : ℝ) (250710280133/500000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33521/262144 : ℝ))) 5 (250710280133/500000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33521/262144 : ℝ))) 6 (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33521/262144 : ℝ))) 7 (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33521/262144 : ℝ)) hmem 8 (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33521/262144 : ℝ))) hcmem 8 (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33521/262144 : ℝ)) (992055663209/1000000000000 : ℝ) (248013915803/250000000000 : ℝ) (100284112053/200000000000 : ℝ) (20056822411/40000000000 : ℝ) (49621054761/62500000000 : ℝ) (158787375239/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0969_exp_lower
  have heNumeric : (1027450883251/500000000000 : ℝ)/4 ≤ Real.exp (-17051297702467/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450883251/500000000000 : ℝ)/4 ≤ Real.exp ((67041/524288 : ℝ)-(158787375239/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67041/524288 : ℝ) (33521/262144 : ℝ) (158787375239/200000000000 : ℝ) (1027450883251/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0970; no trusted numerical premise.
theorem cover8_leaf0970_exp_radius : (998003957647540311/1000000000000000000 : ℝ) ≤ Real.exp ((-67043/4194304 : ℝ)/8) ∧ Real.exp ((-67043/4194304 : ℝ)/8) ≤ (124750494705942539/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67043/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0970_exp_lower : (18402269221316879/20000000000000000 : ℝ) ≤ Real.exp ((-42628244120447/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628244120447/64000000000000 : ℝ)/8) ≤ (920113461065843951/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628244120447/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0970_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745088543/50000000000 : ℝ) ≤ 4*Real.exp (33521/262144 : ℝ)*Real.exp (-mu (radius 8 (67043/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (102745088543/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67043/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0970_exp_radius
  have hrNumeric : (492071387063/500000000000 : ℝ) ≤ Real.exp (-67043/4194304 : ℝ) ∧ Real.exp (-67043/4194304 : ℝ) ≤ (984142774127/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492071387063/500000000000 : ℝ) ≤ (radius 8 (67043/524288 : ℝ)) ∧ (radius 8 (67043/524288 : ℝ)) ≤ (984142774127/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67043/524288 : ℝ)) (492071387063/500000000000 : ℝ) (984142774127/1000000000000 : ℝ) (177378127551/1000000000000 : ℝ) (177378127557/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67043/524288 : ℝ)) (492071387063/500000000000 : ℝ) (984142774127/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67043/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492071387063/500000000000 : ℝ) (984142774127/1000000000000 : ℝ) (992071387063/1000000000000 : ℝ) (124008923383/125000000000 : ℝ) (496019851953/500000000000 : ℝ) (992039703907/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67043/524288 : ℝ)) 1 (992071387063/1000000000000 : ℝ) (124008923383/125000000000 : ℝ) (496019851953/500000000000 : ℝ) (992039703907/1000000000000 : ℝ) (248013886371/250000000000 : ℝ) (496027772743/500000000000 : ℝ) (496027772679/500000000000 : ℝ) (12400694317/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67043/524288 : ℝ)) 2 (248013886371/250000000000 : ℝ) (496027772743/500000000000 : ℝ) (496027772679/500000000000 : ℝ) (12400694317/12500000000 : ℝ) (992055545421/1000000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67043/524288 : ℝ)) 3 (992055545421/1000000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67043/524288 : ℝ)) 4 (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67043/524288 : ℝ)) 5 (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67043/524288 : ℝ)) 6 (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67043/524288 : ℝ)) 7 (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67043/524288 : ℝ))) (177378127551/1000000000000 : ℝ) (177378127557/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67043/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177378127551/1000000000000 : ℝ) (177378127557/1000000000000 : ℝ) (23547562551/40000000000 : ℝ) (588689063779/1000000000000 : ℝ) (105290706959/250000000000 : ℝ) (105290706961/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67043/524288 : ℝ))) 1 (23547562551/40000000000 : ℝ) (588689063779/1000000000000 : ℝ) (105290706959/250000000000 : ℝ) (105290706961/250000000000 : ℝ) (100985189161/200000000000 : ℝ) (126231486453/250000000000 : ℝ) (248964832263/500000000000 : ℝ) (248964832267/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67043/524288 : ℝ))) 2 (100985189161/200000000000 : ℝ) (126231486453/250000000000 : ℝ) (248964832263/500000000000 : ℝ) (248964832267/500000000000 : ℝ) (100285561033/200000000000 : ℝ) (501427805173/1000000000000 : ℝ) (501415602873/1000000000000 : ℝ) (250707801441/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67043/524288 : ℝ))) 3 (100285561033/200000000000 : ℝ) (501427805173/1000000000000 : ℝ) (501415602873/1000000000000 : ℝ) (250707801441/500000000000 : ℝ) (501421704019/1000000000000 : ℝ) (125355426007/250000000000 : ℝ) (501421703981/1000000000000 : ℝ) (501421703991/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67043/524288 : ℝ))) 4 (501421704019/1000000000000 : ℝ) (125355426007/250000000000 : ℝ) (501421703981/1000000000000 : ℝ) (501421703991/1000000000000 : ℝ) (62677713/125000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67043/524288 : ℝ))) 5 (62677713/125000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67043/524288 : ℝ))) 6 (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67043/524288 : ℝ))) 7 (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67043/524288 : ℝ)) hmem 8 (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67043/524288 : ℝ))) hcmem 8 (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67043/524288 : ℝ)) (49602777271/50000000000 : ℝ) (992055545423/1000000000000 : ℝ) (501421703999/1000000000000 : ℝ) (50142170401/100000000000 : ℝ) (396969390701/500000000000 : ℝ) (793938781423/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0970_exp_lower
  have heNumeric : (102745088543/50000000000 : ℝ)/4 ≤ Real.exp (-42628244120447/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745088543/50000000000 : ℝ)/4 ≤ Real.exp ((33521/262144 : ℝ)-(793938781423/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33521/262144 : ℝ) (67043/524288 : ℝ) (793938781423/1000000000000 : ℝ) (102745088543/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0971; no trusted numerical premise.
theorem cover8_leaf0971_exp_radius : (124750490988088133/125000000000000000 : ℝ) ≤ Real.exp ((-16761/1048576 : ℝ)/8) ∧ Real.exp ((-16761/1048576 : ℝ)/8) ≤ (199600785580941013/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16761/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0971_exp_lower : (92011346131112697/100000000000000000 : ℝ) ≤ Real.exp ((-85256487967917/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256487967917/128000000000000 : ℝ)/8) ≤ (920113461311126971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256487967917/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0971_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450887621/500000000000 : ℝ) ≤ 4*Real.exp (67043/524288 : ℝ)*Real.exp (-mu (radius 8 (16761/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450887621/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16761/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0971_exp_radius
  have hrNumeric : (30754454359/31250000000 : ℝ) ≤ Real.exp (-16761/1048576 : ℝ) ∧ Real.exp (-16761/1048576 : ℝ) ≤ (984142539489/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30754454359/31250000000 : ℝ) ≤ (radius 8 (16761/131072 : ℝ)) ∧ (radius 8 (16761/131072 : ℝ)) ≤ (984142539489/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16761/131072 : ℝ)) (30754454359/31250000000 : ℝ) (984142539489/1000000000000 : ℝ) (88689714691/500000000000 : ℝ) (177379429389/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16761/131072 : ℝ)) (30754454359/31250000000 : ℝ) (984142539489/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16761/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30754454359/31250000000 : ℝ) (984142539489/1000000000000 : ℝ) (62004454359/62500000000 : ℝ) (198414253949/200000000000 : ℝ) (198407917129/200000000000 : ℝ) (992039585647/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16761/131072 : ℝ)) 1 (62004454359/62500000000 : ℝ) (198414253949/200000000000 : ℝ) (198407917129/200000000000 : ℝ) (992039585647/1000000000000 : ℝ) (496027713847/500000000000 : ℝ) (62003464231/62500000000 : ℝ) (62003464223/62500000000 : ℝ) (99205542757/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16761/131072 : ℝ)) 2 (496027713847/500000000000 : ℝ) (62003464231/62500000000 : ℝ) (62003464223/62500000000 : ℝ) (99205542757/100000000000 : ℝ) (992055427631/1000000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16761/131072 : ℝ)) 3 (992055427631/1000000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16761/131072 : ℝ)) 4 (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16761/131072 : ℝ)) 5 (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16761/131072 : ℝ)) 6 (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16761/131072 : ℝ)) 7 (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16761/131072 : ℝ))) (88689714691/500000000000 : ℝ) (177379429389/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16761/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88689714691/500000000000 : ℝ) (177379429389/1000000000000 : ℝ) (588689714691/1000000000000 : ℝ) (117737942939/200000000000 : ℝ) (421164373353/1000000000000 : ℝ) (210582186681/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16761/131072 : ℝ))) 1 (588689714691/1000000000000 : ℝ) (117737942939/200000000000 : ℝ) (421164373353/1000000000000 : ℝ) (210582186681/500000000000 : ℝ) (252463522011/500000000000 : ℝ) (504927044029/1000000000000 : ℝ) (497930853419/1000000000000 : ℝ) (497930853427/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16761/131072 : ℝ))) 2 (252463522011/500000000000 : ℝ) (504927044029/1000000000000 : ℝ) (497930853419/1000000000000 : ℝ) (497930853427/1000000000000 : ℝ) (6267861859/12500000000 : ℝ) (62678618591/125000000000 : ℝ) (125354186693/250000000000 : ℝ) (501416746781/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16761/131072 : ℝ))) 3 (6267861859/12500000000 : ℝ) (62678618591/125000000000 : ℝ) (125354186693/250000000000 : ℝ) (501416746781/1000000000000 : ℝ) (250711423873/500000000000 : ℝ) (100284569551/200000000000 : ℝ) (125355711927/250000000000 : ℝ) (250711423859/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16761/131072 : ℝ))) 4 (250711423873/500000000000 : ℝ) (100284569551/200000000000 : ℝ) (125355711927/250000000000 : ℝ) (250711423859/500000000000 : ℝ) (501422847727/1000000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16761/131072 : ℝ))) 5 (501422847727/1000000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16761/131072 : ℝ))) 6 (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16761/131072 : ℝ))) 7 (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16761/131072 : ℝ)) hmem 8 (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16761/131072 : ℝ))) hcmem 8 (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16761/131072 : ℝ)) (99205542763/100000000000 : ℝ) (992055427633/1000000000000 : ℝ) (250711423863/500000000000 : ℝ) (501422847737/1000000000000 : ℝ) (396970343309/500000000000 : ℝ) (793940686639/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0971_exp_lower
  have heNumeric : (1027450887621/500000000000 : ℝ)/4 ≤ Real.exp (-85256487967917/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450887621/500000000000 : ℝ)/4 ≤ Real.exp ((67043/524288 : ℝ)-(793940686639/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67043/524288 : ℝ) (16761/131072 : ℝ) (793940686639/1000000000000 : ℝ) (1027450887621/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0972; no trusted numerical premise.
theorem cover8_leaf0972_exp_radius : (62375243635116919/62500000000000000 : ℝ) ≤ Real.exp ((-67045/4194304 : ℝ)/8) ∧ Real.exp ((-67045/4194304 : ℝ)/8) ≤ (199600779632374141/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67045/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0972_exp_lower : (460056730779470151/500000000000000000 : ℝ) ≤ Real.exp ((-21314121923031/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314121923031/32000000000000 : ℝ)/8) ≤ (920113461558940303/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314121923031/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0972_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490177967/100000000000 : ℝ) ≤ 4*Real.exp (16761/131072 : ℝ)*Real.exp (-mu (radius 8 (67045/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490177967/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67045/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0972_exp_radius
  have hrNumeric : (19682846097/20000000000 : ℝ) ≤ Real.exp (-67045/4194304 : ℝ) ∧ Real.exp (-67045/4194304 : ℝ) ≤ (984142304851/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19682846097/20000000000 : ℝ) ≤ (radius 8 (67045/524288 : ℝ)) ∧ (radius 8 (67045/524288 : ℝ)) ≤ (984142304851/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67045/524288 : ℝ)) (19682846097/20000000000 : ℝ) (984142304851/1000000000000 : ℝ) (44345182801/250000000000 : ℝ) (17738073121/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67045/524288 : ℝ)) (19682846097/20000000000 : ℝ) (984142304851/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67045/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19682846097/20000000000 : ℝ) (984142304851/1000000000000 : ℝ) (39682846097/40000000000 : ℝ) (496035576213/500000000000 : ℝ) (198407893477/200000000000 : ℝ) (496019733693/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67045/524288 : ℝ)) 1 (39682846097/40000000000 : ℝ) (496035576213/500000000000 : ℝ) (198407893477/200000000000 : ℝ) (496019733693/500000000000 : ℝ) (198411061981/200000000000 : ℝ) (496027654953/500000000000 : ℝ) (496027654889/500000000000 : ℝ) (49602765489/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67045/524288 : ℝ)) 2 (198411061981/200000000000 : ℝ) (496027654953/500000000000 : ℝ) (496027654889/500000000000 : ℝ) (49602765489/50000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67045/524288 : ℝ)) 3 (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67045/524288 : ℝ)) 4 (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67045/524288 : ℝ)) 5 (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67045/524288 : ℝ)) 6 (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67045/524288 : ℝ)) 7 (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67045/524288 : ℝ))) (44345182801/250000000000 : ℝ) (17738073121/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67045/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44345182801/250000000000 : ℝ) (17738073121/100000000000 : ℝ) (294345182801/500000000000 : ℝ) (117738073121/200000000000 : ℝ) (421165918853/1000000000000 : ℝ) (421165918861/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67045/524288 : ℝ))) 1 (294345182801/500000000000 : ℝ) (117738073121/200000000000 : ℝ) (421165918853/1000000000000 : ℝ) (421165918861/1000000000000 : ℝ) (504928142227/1000000000000 : ℝ) (504928142233/1000000000000 : ℝ) (497932042299/1000000000000 : ℝ) (248966021153/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67045/524288 : ℝ))) 2 (504928142227/1000000000000 : ℝ) (504928142233/1000000000000 : ℝ) (497932042299/1000000000000 : ℝ) (248966021153/500000000000 : ℝ) (501430092263/1000000000000 : ℝ) (50143009227/100000000000 : ℝ) (501417890659/1000000000000 : ℝ) (250708945333/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67045/524288 : ℝ))) 3 (501430092263/1000000000000 : ℝ) (50143009227/100000000000 : ℝ) (501417890659/1000000000000 : ℝ) (250708945333/500000000000 : ℝ) (501423991461/1000000000000 : ℝ) (125355997867/250000000000 : ℝ) (501423991423/1000000000000 : ℝ) (501423991431/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67045/524288 : ℝ))) 4 (501423991461/1000000000000 : ℝ) (125355997867/250000000000 : ℝ) (501423991423/1000000000000 : ℝ) (501423991431/1000000000000 : ℝ) (250711995721/500000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67045/524288 : ℝ))) 5 (250711995721/500000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67045/524288 : ℝ))) 6 (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67045/524288 : ℝ))) 7 (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67045/524288 : ℝ)) hmem 8 (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67045/524288 : ℝ))) hcmem 8 (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67045/524288 : ℝ)) (992055309841/1000000000000 : ℝ) (992055309843/1000000000000 : ℝ) (501423991441/1000000000000 : ℝ) (10028479829/20000000000 : ℝ) (99242823977/125000000000 : ℝ) (793942591833/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0972_exp_lower
  have heNumeric : (205490177967/100000000000 : ℝ)/4 ≤ Real.exp (-21314121923031/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490177967/100000000000 : ℝ)/4 ≤ Real.exp ((16761/131072 : ℝ)-(793942591833/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16761/131072 : ℝ) (67045/524288 : ℝ) (793942591833/1000000000000 : ℝ) (205490177967/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0973; no trusted numerical premise.
theorem cover8_leaf0973_exp_radius : (99800386841903723/100000000000000000 : ℝ) ≤ Real.exp ((-33523/2097152 : ℝ)/8) ∧ Real.exp ((-33523/2097152 : ℝ)/8) ≤ (998003868419037231/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33523/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0973_exp_lower : (920113461808248819/1000000000000000000 : ℝ) ≤ Real.exp ((-85256487414667/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256487414667/128000000000000 : ℝ)/8) ≤ (46005673090412441/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256487414667/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0973_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725446031/250000000000 : ℝ) ≤ 4*Real.exp (67045/524288 : ℝ)*Real.exp (-mu (radius 8 (33523/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725446031/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33523/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0973_exp_radius
  have hrNumeric : (246035517553/250000000000 : ℝ) ≤ Real.exp (-33523/2097152 : ℝ) ∧ Real.exp (-33523/2097152 : ℝ) ≤ (984142070213/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246035517553/250000000000 : ℝ) ≤ (radius 8 (33523/262144 : ℝ)) ∧ (radius 8 (33523/262144 : ℝ)) ≤ (984142070213/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33523/262144 : ℝ)) (246035517553/250000000000 : ℝ) (984142070213/1000000000000 : ℝ) (35476406603/200000000000 : ℝ) (88691016511/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33523/262144 : ℝ)) (246035517553/250000000000 : ℝ) (984142070213/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33523/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246035517553/250000000000 : ℝ) (984142070213/1000000000000 : ℝ) (496035517553/500000000000 : ℝ) (992071035107/1000000000000 : ℝ) (248009837281/250000000000 : ℝ) (496019674563/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33523/262144 : ℝ)) 1 (496035517553/500000000000 : ℝ) (992071035107/1000000000000 : ℝ) (248009837281/250000000000 : ℝ) (496019674563/500000000000 : ℝ) (198411038423/200000000000 : ℝ) (992055192117/1000000000000 : ℝ) (248013797997/250000000000 : ℝ) (99205519199/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33523/262144 : ℝ)) 2 (198411038423/200000000000 : ℝ) (992055192117/1000000000000 : ℝ) (248013797997/250000000000 : ℝ) (99205519199/100000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33523/262144 : ℝ)) 3 (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33523/262144 : ℝ)) 4 (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33523/262144 : ℝ)) 5 (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33523/262144 : ℝ)) 6 (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33523/262144 : ℝ)) 7 (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33523/262144 : ℝ))) (35476406603/200000000000 : ℝ) (88691016511/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33523/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35476406603/200000000000 : ℝ) (88691016511/500000000000 : ℝ) (588691016507/1000000000000 : ℝ) (588691016511/1000000000000 : ℝ) (84233492867/200000000000 : ℝ) (84233492869/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33523/262144 : ℝ))) 1 (588691016507/1000000000000 : ℝ) (588691016511/1000000000000 : ℝ) (84233492867/200000000000 : ℝ) (84233492869/200000000000 : ℝ) (504929240421/1000000000000 : ℝ) (126232310107/250000000000 : ℝ) (99586646233/200000000000 : ℝ) (248966615587/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33523/262144 : ℝ))) 2 (504929240421/1000000000000 : ℝ) (126232310107/250000000000 : ℝ) (99586646233/200000000000 : ℝ) (248966615587/500000000000 : ℝ) (501431235793/1000000000000 : ℝ) (501431235801/1000000000000 : ℝ) (501419034533/1000000000000 : ℝ) (250709517271/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33523/262144 : ℝ))) 3 (501431235793/1000000000000 : ℝ) (501431235801/1000000000000 : ℝ) (501419034533/1000000000000 : ℝ) (250709517271/500000000000 : ℝ) (501425135163/1000000000000 : ℝ) (125356283793/250000000000 : ℝ) (4011401081/8000000000 : ℝ) (100285027027/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33523/262144 : ℝ))) 4 (501425135163/1000000000000 : ℝ) (125356283793/250000000000 : ℝ) (4011401081/8000000000 : ℝ) (100285027027/200000000000 : ℝ) (62678141893/125000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33523/262144 : ℝ))) 5 (62678141893/125000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33523/262144 : ℝ))) 6 (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33523/262144 : ℝ))) 7 (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33523/262144 : ℝ)) hmem 8 (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33523/262144 : ℝ))) hcmem 8 (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33523/262144 : ℝ)) (992055192051/1000000000000 : ℝ) (496027596027/500000000000 : ℝ) (501425135143/1000000000000 : ℝ) (250712567577/500000000000 : ℝ) (793944496993/1000000000000 : ℝ) (396972248507/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0973_exp_lower
  have heNumeric : (513725446031/250000000000 : ℝ)/4 ≤ Real.exp (-85256487414667/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725446031/250000000000 : ℝ)/4 ≤ Real.exp ((67045/524288 : ℝ)-(396972248507/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67045/524288 : ℝ) (33523/262144 : ℝ) (396972248507/500000000000 : ℝ) (513725446031/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0974; no trusted numerical premise.
theorem cover8_leaf0974_exp_radius : (499001919338102321/500000000000000000 : ℝ) ≤ Real.exp ((-67047/4194304 : ℝ)/8) ∧ Real.exp ((-67047/4194304 : ℝ)/8) ≤ (998003838676204643/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67047/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0974_exp_lower : (920113462060087647/1000000000000000000 : ℝ) ≤ Real.exp ((-42628243567197/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628243567197/64000000000000 : ℝ)/8) ≤ (28753545689377739/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628243567197/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0974_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431361789/62500000000 : ℝ) ≤ 4*Real.exp (33523/262144 : ℝ)*Real.exp (-mu (radius 8 (67047/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431361789/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67047/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0974_exp_radius
  have hrNumeric : (492070917787/500000000000 : ℝ) ≤ Real.exp (-67047/4194304 : ℝ) ∧ Real.exp (-67047/4194304 : ℝ) ≤ (39365673423/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492070917787/500000000000 : ℝ) ≤ (radius 8 (67047/524288 : ℝ)) ∧ (radius 8 (67047/524288 : ℝ)) ≤ (39365673423/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67047/524288 : ℝ)) (492070917787/500000000000 : ℝ) (39365673423/40000000000 : ℝ) (177383334817/1000000000000 : ℝ) (22172916853/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67047/524288 : ℝ)) (492070917787/500000000000 : ℝ) (39365673423/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67047/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492070917787/500000000000 : ℝ) (39365673423/40000000000 : ℝ) (992070917787/1000000000000 : ℝ) (248017729447/250000000000 : ℝ) (62002451929/62500000000 : ℝ) (198407846173/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67047/524288 : ℝ)) 1 (992070917787/1000000000000 : ℝ) (248017729447/250000000000 : ℝ) (62002451929/62500000000 : ℝ) (198407846173/200000000000 : ℝ) (39682202973/40000000000 : ℝ) (992055074327/1000000000000 : ℝ) (496027537099/500000000000 : ℝ) (4960275371/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67047/524288 : ℝ)) 2 (39682202973/40000000000 : ℝ) (992055074327/1000000000000 : ℝ) (496027537099/500000000000 : ℝ) (4960275371/5000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67047/524288 : ℝ)) 3 (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67047/524288 : ℝ)) 4 (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67047/524288 : ℝ)) 5 (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67047/524288 : ℝ)) 6 (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67047/524288 : ℝ)) 7 (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67047/524288 : ℝ))) (177383334817/1000000000000 : ℝ) (22172916853/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67047/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177383334817/1000000000000 : ℝ) (22172916853/125000000000 : ℝ) (36793229213/62500000000 : ℝ) (147172916853/250000000000 : ℝ) (421169009801/1000000000000 : ℝ) (42116900981/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67047/524288 : ℝ))) 1 (36793229213/62500000000 : ℝ) (147172916853/250000000000 : ℝ) (421169009801/1000000000000 : ℝ) (42116900981/100000000000 : ℝ) (126232584651/250000000000 : ℝ) (504930338611/1000000000000 : ℝ) (497934420019/1000000000000 : ℝ) (497934420027/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67047/524288 : ℝ))) 2 (126232584651/250000000000 : ℝ) (504930338611/1000000000000 : ℝ) (497934420019/1000000000000 : ℝ) (497934420027/1000000000000 : ℝ) (501432379311/1000000000000 : ℝ) (501432379319/1000000000000 : ℝ) (125355044599/250000000000 : ℝ) (125355044601/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67047/524288 : ℝ))) 3 (501432379311/1000000000000 : ℝ) (501432379319/1000000000000 : ℝ) (125355044599/250000000000 : ℝ) (125355044601/250000000000 : ℝ) (501426278853/1000000000000 : ℝ) (250713139431/500000000000 : ℝ) (15669571213/31250000000 : ℝ) (20057051153/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67047/524288 : ℝ))) 4 (501426278853/1000000000000 : ℝ) (250713139431/500000000000 : ℝ) (15669571213/31250000000 : ℝ) (20057051153/40000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67047/524288 : ℝ))) 5 (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67047/524288 : ℝ))) 6 (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67047/524288 : ℝ))) 7 (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67047/524288 : ℝ)) hmem 8 (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67047/524288 : ℝ))) hcmem 8 (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67047/524288 : ℝ)) (992055074261/1000000000000 : ℝ) (124006884283/125000000000 : ℝ) (250713139417/500000000000 : ℝ) (125356569711/250000000000 : ℝ) (396973201077/500000000000 : ℝ) (793946402173/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0974_exp_lower
  have heNumeric : (128431361789/62500000000 : ℝ)/4 ≤ Real.exp (-42628243567197/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431361789/62500000000 : ℝ)/4 ≤ Real.exp ((33523/262144 : ℝ)-(793946402173/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33523/262144 : ℝ) (67047/524288 : ℝ) (793946402173/1000000000000 : ℝ) (128431361789/62500000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0950_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0950_certificate
#check SmaleRate.Proofs.cover8_leaf0951_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0951_certificate
#check SmaleRate.Proofs.cover8_leaf0952_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0952_certificate
#check SmaleRate.Proofs.cover8_leaf0953_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0953_certificate
#check SmaleRate.Proofs.cover8_leaf0954_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0954_certificate
#check SmaleRate.Proofs.cover8_leaf0955_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0955_certificate
#check SmaleRate.Proofs.cover8_leaf0956_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0956_certificate
#check SmaleRate.Proofs.cover8_leaf0957_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0957_certificate
#check SmaleRate.Proofs.cover8_leaf0958_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0958_certificate
#check SmaleRate.Proofs.cover8_leaf0959_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0959_certificate
#check SmaleRate.Proofs.cover8_leaf0960_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0960_certificate
#check SmaleRate.Proofs.cover8_leaf0961_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0961_certificate
#check SmaleRate.Proofs.cover8_leaf0962_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0962_certificate
#check SmaleRate.Proofs.cover8_leaf0963_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0963_certificate
#check SmaleRate.Proofs.cover8_leaf0964_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0964_certificate
#check SmaleRate.Proofs.cover8_leaf0965_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0965_certificate
#check SmaleRate.Proofs.cover8_leaf0966_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0966_certificate
#check SmaleRate.Proofs.cover8_leaf0967_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0967_certificate
#check SmaleRate.Proofs.cover8_leaf0968_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0968_certificate
#check SmaleRate.Proofs.cover8_leaf0969_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0969_certificate
#check SmaleRate.Proofs.cover8_leaf0970_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0970_certificate
#check SmaleRate.Proofs.cover8_leaf0971_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0971_certificate
#check SmaleRate.Proofs.cover8_leaf0972_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0972_certificate
#check SmaleRate.Proofs.cover8_leaf0973_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0973_certificate
#check SmaleRate.Proofs.cover8_leaf0974_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0974_certificate
