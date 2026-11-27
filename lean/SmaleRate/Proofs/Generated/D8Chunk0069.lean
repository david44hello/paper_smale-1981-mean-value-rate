/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1725; no trusted numerical premise.
theorem cover8_leaf1725_exp_radius : (249238223516758327/250000000000000000 : ℝ) ≤ Real.exp ((-25/1024 : ℝ)/8) ∧ Real.exp ((-25/1024 : ℝ)/8) ≤ (996952894067033309/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-25/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1725_exp_lower : (460147055325892097/500000000000000000 : ℝ) ≤ Real.exp ((-166123949073/250000000000 : ℝ)/8) ∧ Real.exp ((-166123949073/250000000000 : ℝ)/8) ≤ (184058822130356839/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166123949073/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1725_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2058131566827/1000000000000 : ℝ) ≤ 4*Real.exp (3/16 : ℝ)*Real.exp (-mu (radius 8 (25/128 : ℝ))) ∧ (20549/10000 : ℝ) < (2058131566827/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (25/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1725_exp_radius
  have hrNumeric : (195176310027/200000000000 : ℝ) ≤ Real.exp (-25/1024 : ℝ) ∧ Real.exp (-25/1024 : ℝ) ≤ (121985193767/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (195176310027/200000000000 : ℝ) ≤ (radius 8 (25/128 : ℝ)) ∧ (radius 8 (25/128 : ℝ)) ≤ (121985193767/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (25/128 : ℝ)) (195176310027/200000000000 : ℝ) (121985193767/125000000000 : ℝ) (218300710269/1000000000000 : ℝ) (109150355137/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (25/128 : ℝ)) (195176310027/200000000000 : ℝ) (121985193767/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (25/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (195176310027/200000000000 : ℝ) (121985193767/125000000000 : ℝ) (987940775067/1000000000000 : ℝ) (246985193767/250000000000 : ℝ) (987867172313/1000000000000 : ℝ) (197573434463/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (25/128 : ℝ)) 1 (987940775067/1000000000000 : ℝ) (246985193767/250000000000 : ℝ) (987867172313/1000000000000 : ℝ) (197573434463/200000000000 : ℝ) (98790397369/100000000000 : ℝ) (246975993423/250000000000 : ℝ) (246975993251/250000000000 : ℝ) (987903973007/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (25/128 : ℝ)) 2 (98790397369/100000000000 : ℝ) (246975993423/250000000000 : ℝ) (246975993251/250000000000 : ℝ) (987903973007/1000000000000 : ℝ) (987903973347/1000000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (25/128 : ℝ)) 3 (987903973347/1000000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (25/128 : ℝ)) 4 (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (25/128 : ℝ)) 5 (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (25/128 : ℝ)) 6 (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (25/128 : ℝ)) 7 (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (25/128 : ℝ))) (218300710269/1000000000000 : ℝ) (109150355137/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (25/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (218300710269/1000000000000 : ℝ) (109150355137/500000000000 : ℝ) (304575177567/500000000000 : ℝ) (609150355137/1000000000000 : ℝ) (23361330777/50000000000 : ℝ) (233613307773/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (25/128 : ℝ))) 1 (304575177567/500000000000 : ℝ) (609150355137/1000000000000 : ℝ) (23361330777/50000000000 : ℝ) (233613307773/500000000000 : ℝ) (538188485337/1000000000000 : ℝ) (269094242671/500000000000 : ℝ) (266744849427/500000000000 : ℝ) (26674484943/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (25/128 : ℝ))) 2 (538188485337/1000000000000 : ℝ) (269094242671/500000000000 : ℝ) (266744849427/500000000000 : ℝ) (26674484943/50000000000 : ℝ) (107167818419/200000000000 : ℝ) (535839092101/1000000000000 : ℝ) (267916970799/500000000000 : ℝ) (107166788321/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (25/128 : ℝ))) 3 (107167818419/200000000000 : ℝ) (535839092101/1000000000000 : ℝ) (267916970799/500000000000 : ℝ) (107166788321/200000000000 : ℝ) (267918258423/500000000000 : ℝ) (535836516853/1000000000000 : ℝ) (13395912921/25000000000 : ℝ) (535836516847/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (25/128 : ℝ))) 4 (267918258423/500000000000 : ℝ) (535836516853/1000000000000 : ℝ) (13395912921/25000000000 : ℝ) (535836516847/1000000000000 : ℝ) (535836516843/1000000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (25/128 : ℝ))) 5 (535836516843/1000000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (25/128 : ℝ))) 6 (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (25/128 : ℝ))) 7 (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (25/128 : ℝ)) hmem 8 (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (25/128 : ℝ))) hcmem 8 (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (25/128 : ℝ)) (493951986673/500000000000 : ℝ) (19758079467/20000000000 : ℝ) (267918258421/500000000000 : ℝ) (10716730337/20000000000 : ℝ) (34079831851/40000000000 : ℝ) (212998949073/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1725_exp_lower
  have heNumeric : (2058131566827/1000000000000 : ℝ)/4 ≤ Real.exp (-166123949073/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2058131566827/1000000000000 : ℝ)/4 ≤ Real.exp ((3/16 : ℝ)-(212998949073/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (3/16 : ℝ) (25/128 : ℝ) (212998949073/250000000000 : ℝ) (2058131566827/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1726; no trusted numerical premise.
theorem cover8_leaf1726_exp_radius : (498415601571641211/500000000000000000 : ℝ) ≤ Real.exp ((-13/512 : ℝ)/8) ∧ Real.exp ((-13/512 : ℝ)/8) ≤ (996831203143282423/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-13/512 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1726_exp_lower : (23013116977586859/25000000000000000 : ℝ) ≤ Real.exp ((-132498349003/200000000000 : ℝ)/8) ∧ Real.exp ((-132498349003/200000000000 : ℝ)/8) ≤ (920524679103474361/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-132498349003/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1726_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (103113015187/50000000000 : ℝ) ≤ 4*Real.exp (25/128 : ℝ)*Real.exp (-mu (radius 8 (13/64 : ℝ))) ∧ (20549/10000 : ℝ) < (103113015187/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (13/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1726_exp_radius
  have hrNumeric : (487464502997/500000000000 : ℝ) ≤ Real.exp (-13/512 : ℝ) ∧ Real.exp (-13/512 : ℝ) ≤ (194985801199/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (487464502997/500000000000 : ℝ) ≤ (radius 8 (13/64 : ℝ)) ∧ (radius 8 (13/64 : ℝ)) ≤ (194985801199/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (13/64 : ℝ)) (487464502997/500000000000 : ℝ) (194985801199/200000000000 : ℝ) (222516141593/1000000000000 : ℝ) (111258070799/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (13/64 : ℝ)) (487464502997/500000000000 : ℝ) (194985801199/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (13/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (487464502997/500000000000 : ℝ) (194985801199/200000000000 : ℝ) (987464502997/1000000000000 : ℝ) (493732251499/500000000000 : ℝ) (987384933039/1000000000000 : ℝ) (987384933041/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (13/64 : ℝ)) 1 (987464502997/1000000000000 : ℝ) (493732251499/500000000000 : ℝ) (987384933039/1000000000000 : ℝ) (987384933041/1000000000000 : ℝ) (493712359009/500000000000 : ℝ) (49371235901/50000000000 : ℝ) (30857022413/31250000000 : ℝ) (493712358609/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (13/64 : ℝ)) 2 (493712359009/500000000000 : ℝ) (49371235901/50000000000 : ℝ) (30857022413/31250000000 : ℝ) (493712358609/500000000000 : ℝ) (987424717617/1000000000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (13/64 : ℝ)) 3 (987424717617/1000000000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (13/64 : ℝ)) 4 (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (13/64 : ℝ)) 5 (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (13/64 : ℝ)) 6 (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (13/64 : ℝ)) 7 (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (13/64 : ℝ))) (222516141593/1000000000000 : ℝ) (111258070799/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (13/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (222516141593/1000000000000 : ℝ) (111258070799/500000000000 : ℝ) (152814517699/250000000000 : ℝ) (611258070799/1000000000000 : ℝ) (235858083173/500000000000 : ℝ) (471716166353/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (13/64 : ℝ))) 1 (152814517699/250000000000 : ℝ) (611258070799/1000000000000 : ℝ) (235858083173/500000000000 : ℝ) (471716166353/1000000000000 : ℝ) (541487118571/1000000000000 : ℝ) (33842944911/62500000000 : ℝ) (107394657931/200000000000 : ℝ) (268486644831/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (13/64 : ℝ))) 2 (541487118571/1000000000000 : ℝ) (33842944911/62500000000 : ℝ) (107394657931/200000000000 : ℝ) (268486644831/500000000000 : ℝ) (539230204113/1000000000000 : ℝ) (539230204119/1000000000000 : ℝ) (134806370251/250000000000 : ℝ) (539225481011/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (13/64 : ℝ))) 3 (539230204113/1000000000000 : ℝ) (539230204119/1000000000000 : ℝ) (134806370251/250000000000 : ℝ) (539225481011/1000000000000 : ℝ) (269613921279/500000000000 : ℝ) (107845568513/200000000000 : ℝ) (539227842553/1000000000000 : ℝ) (52658969/97656250 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (13/64 : ℝ))) 4 (269613921279/500000000000 : ℝ) (107845568513/200000000000 : ℝ) (539227842553/1000000000000 : ℝ) (52658969/97656250 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (13/64 : ℝ))) 5 (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (13/64 : ℝ))) 6 (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (13/64 : ℝ))) 7 (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (13/64 : ℝ)) hmem 8 (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (13/64 : ℝ))) hcmem 8 (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (13/64 : ℝ)) (61714044851/62500000000 : ℝ) (987424717619/1000000000000 : ℝ) (107845568511/200000000000 : ℝ) (539227842563/1000000000000 : ℝ) (857804244999/1000000000000 : ℝ) (171560849003/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1726_exp_lower
  have heNumeric : (103113015187/50000000000 : ℝ)/4 ≤ Real.exp (-132498349003/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (103113015187/50000000000 : ℝ)/4 ≤ Real.exp ((25/128 : ℝ)-(171560849003/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (25/128 : ℝ) (13/64 : ℝ) (171560849003/200000000000 : ℝ) (103113015187/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1727; no trusted numerical premise.
theorem cover8_leaf1727_exp_radius : (199317573171158983/200000000000000000 : ℝ) ≤ Real.exp ((-7/256 : ℝ)/8) ∧ Real.exp ((-7/256 : ℝ)/8) ≤ (249146966463948729/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-7/256 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1727_exp_lower : (184027130770874731/200000000000000000 : ℝ) ≤ Real.exp ((-83234169967/125000000000 : ℝ)/8) ∧ Real.exp ((-83234169967/125000000000 : ℝ)/8) ≤ (115016956731796707/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83234169967/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1727_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51382457799/25000000000 : ℝ) ≤ 4*Real.exp (13/64 : ℝ)*Real.exp (-mu (radius 8 (7/32 : ℝ))) ∧ (20549/10000 : ℝ) < (51382457799/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (7/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1727_exp_radius
  have hrNumeric : (973026706099/1000000000000 : ℝ) ≤ Real.exp (-7/256 : ℝ) ∧ Real.exp (-7/256 : ℝ) ≤ (9730267061/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (973026706099/1000000000000 : ℝ) ≤ (radius 8 (7/32 : ℝ)) ∧ (radius 8 (7/32 : ℝ)) ≤ (9730267061/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (7/32 : ℝ)) (973026706099/1000000000000 : ℝ) (9730267061/10000000000 : ℝ) (115346249631/500000000000 : ℝ) (57673124817/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (7/32 : ℝ)) (973026706099/1000000000000 : ℝ) (9730267061/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (7/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (973026706099/1000000000000 : ℝ) (9730267061/10000000000 : ℝ) (986513353049/1000000000000 : ℝ) (19730267061/20000000000 : ℝ) (986421160609/1000000000000 : ℝ) (986421160611/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (7/32 : ℝ)) 1 (986513353049/1000000000000 : ℝ) (19730267061/20000000000 : ℝ) (986421160609/1000000000000 : ℝ) (986421160611/1000000000000 : ℝ) (986467256829/1000000000000 : ℝ) (986467256831/1000000000000 : ℝ) (986467255751/1000000000000 : ℝ) (493233627877/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (7/32 : ℝ)) 2 (986467256829/1000000000000 : ℝ) (986467256831/1000000000000 : ℝ) (986467255751/1000000000000 : ℝ) (493233627877/500000000000 : ℝ) (98646725629/100000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (7/32 : ℝ)) 3 (98646725629/100000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (7/32 : ℝ)) 4 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (7/32 : ℝ)) 5 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (7/32 : ℝ)) 6 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (7/32 : ℝ)) 7 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (7/32 : ℝ))) (115346249631/500000000000 : ℝ) (57673124817/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (7/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (115346249631/500000000000 : ℝ) (57673124817/250000000000 : ℝ) (615346249631/1000000000000 : ℝ) (307673124817/500000000000 : ℝ) (48030459009/100000000000 : ℝ) (480304590097/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (7/32 : ℝ))) 1 (615346249631/1000000000000 : ℝ) (307673124817/500000000000 : ℝ) (48030459009/100000000000 : ℝ) (480304590097/1000000000000 : ℝ) (27391270993/50000000000 : ℝ) (273912709933/500000000000 : ℝ) (543648441727/1000000000000 : ℝ) (543648441733/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (7/32 : ℝ))) 2 (27391270993/50000000000 : ℝ) (273912709933/500000000000 : ℝ) (543648441727/1000000000000 : ℝ) (543648441733/1000000000000 : ℝ) (545736930793/1000000000000 : ℝ) (1364342327/2500000000 : ℝ) (545732934543/1000000000000 : ℝ) (10914658691/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (7/32 : ℝ))) 3 (545736930793/1000000000000 : ℝ) (1364342327/2500000000 : ℝ) (545732934543/1000000000000 : ℝ) (10914658691/20000000000 : ℝ) (136433733167/250000000000 : ℝ) (21829397307/40000000000 : ℝ) (68216866583/125000000000 : ℝ) (8527108323/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (7/32 : ℝ))) 4 (136433733167/250000000000 : ℝ) (21829397307/40000000000 : ℝ) (68216866583/125000000000 : ℝ) (8527108323/15625000000 : ℝ) (272867466333/500000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (7/32 : ℝ))) 5 (272867466333/500000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (7/32 : ℝ))) 6 (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (7/32 : ℝ))) 7 (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (7/32 : ℝ)) hmem 8 (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (7/32 : ℝ))) hcmem 8 (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (7/32 : ℝ)) (986467256289/1000000000000 : ℝ) (986467256293/1000000000000 : ℝ) (109146986533/200000000000 : ℝ) (272867466337/500000000000 : ℝ) (868998359717/1000000000000 : ℝ) (108624794967/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1727_exp_lower
  have heNumeric : (51382457799/25000000000 : ℝ)/4 ≤ Real.exp (-83234169967/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51382457799/25000000000 : ℝ)/4 ≤ Real.exp ((13/64 : ℝ)-(108624794967/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (13/64 : ℝ) (7/32 : ℝ) (108624794967/125000000000 : ℝ) (51382457799/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1728; no trusted numerical premise.
theorem cover8_leaf1728_exp_radius : (199268917593914687/200000000000000000 : ℝ) ≤ Real.exp ((-15/512 : ℝ)/8) ∧ Real.exp ((-15/512 : ℝ)/8) ≤ (249086146992393359/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-15/512 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1728_exp_lower : (115087969109398149/125000000000000000 : ℝ) ≤ Real.exp ((-660935620687/1000000000000 : ℝ)/8) ∧ Real.exp ((-660935620687/1000000000000 : ℝ)/8) ≤ (920703752875185193/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-660935620687/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1728_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (206547193537/100000000000 : ℝ) ≤ 4*Real.exp (7/32 : ℝ)*Real.exp (-mu (radius 8 (15/64 : ℝ))) ∧ (20549/10000 : ℝ) < (206547193537/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (15/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1728_exp_radius
  have hrNumeric : (971128118007/1000000000000 : ℝ) ≤ Real.exp (-15/512 : ℝ) ∧ Real.exp (-15/512 : ℝ) ≤ (121391014751/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (971128118007/1000000000000 : ℝ) ≤ (radius 8 (15/64 : ℝ)) ∧ (radius 8 (15/64 : ℝ)) ≤ (121391014751/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (15/64 : ℝ)) (971128118007/1000000000000 : ℝ) (121391014751/125000000000 : ℝ) (238558542949/1000000000000 : ℝ) (119279271477/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (15/64 : ℝ)) (971128118007/1000000000000 : ℝ) (121391014751/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (15/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (971128118007/1000000000000 : ℝ) (121391014751/125000000000 : ℝ) (985564059003/1000000000000 : ℝ) (246391014751/250000000000 : ℝ) (123182291113/125000000000 : ℝ) (197091665781/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (15/64 : ℝ)) 1 (985564059003/1000000000000 : ℝ) (246391014751/250000000000 : ℝ) (123182291113/125000000000 : ℝ) (197091665781/200000000000 : ℝ) (985511193953/1000000000000 : ℝ) (197102238791/200000000000 : ℝ) (197102238507/200000000000 : ℝ) (985511192537/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (15/64 : ℝ)) 2 (985511193953/1000000000000 : ℝ) (197102238791/200000000000 : ℝ) (197102238507/200000000000 : ℝ) (985511192537/1000000000000 : ℝ) (246377798311/250000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (15/64 : ℝ)) 3 (246377798311/250000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (15/64 : ℝ)) 4 (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (15/64 : ℝ)) 5 (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (15/64 : ℝ)) 6 (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (15/64 : ℝ)) 7 (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (15/64 : ℝ))) (238558542949/1000000000000 : ℝ) (119279271477/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (15/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (238558542949/1000000000000 : ℝ) (119279271477/500000000000 : ℝ) (309639635737/500000000000 : ℝ) (619279271477/1000000000000 : ℝ) (488424551951/1000000000000 : ℝ) (488424551957/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (15/64 : ℝ))) 1 (309639635737/500000000000 : ℝ) (619279271477/1000000000000 : ℝ) (488424551951/1000000000000 : ℝ) (488424551957/1000000000000 : ℝ) (17307872241/31250000000 : ℝ) (553851911717/1000000000000 : ℝ) (549973818197/1000000000000 : ℝ) (274986909101/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (15/64 : ℝ))) 2 (17307872241/31250000000 : ℝ) (553851911717/1000000000000 : ℝ) (549973818197/1000000000000 : ℝ) (274986909101/500000000000 : ℝ) (275956432477/500000000000 : ℝ) (1724727703/3125000000 : ℝ) (551909458697/1000000000000 : ℝ) (551909458703/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (15/64 : ℝ))) 3 (275956432477/500000000000 : ℝ) (1724727703/3125000000 : ℝ) (551909458697/1000000000000 : ℝ) (551909458703/1000000000000 : ℝ) (22076446473/40000000000 : ℝ) (68988895229/125000000000 : ℝ) (275955580911/500000000000 : ℝ) (551911161829/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (15/64 : ℝ))) 4 (22076446473/40000000000 : ℝ) (68988895229/125000000000 : ℝ) (275955580911/500000000000 : ℝ) (551911161829/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (15/64 : ℝ))) 5 (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (15/64 : ℝ))) 6 (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (15/64 : ℝ))) 7 (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (15/64 : ℝ)) hmem 8 (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (15/64 : ℝ))) hcmem 8 (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (15/64 : ℝ)) (985511193243/1000000000000 : ℝ) (492755596623/500000000000 : ℝ) (551911161823/1000000000000 : ℝ) (551911161831/1000000000000 : ℝ) (87968562067/100000000000 : ℝ) (879685620687/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1728_exp_lower
  have heNumeric : (206547193537/100000000000 : ℝ)/4 ≤ Real.exp (-660935620687/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (206547193537/100000000000 : ℝ)/4 ≤ Real.exp ((7/32 : ℝ)-(879685620687/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (7/32 : ℝ) (15/64 : ℝ) (879685620687/1000000000000 : ℝ) (206547193537/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1729; no trusted numerical premise.
theorem cover8_leaf1729_exp_radius : (99610136947011749/100000000000000000 : ℝ) ≤ Real.exp ((-1/32 : ℝ)/8) ∧ Real.exp ((-1/32 : ℝ)/8) ≤ (996101369470117491/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/32 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1729_exp_lower : (460661973318235591/500000000000000000 : ℝ) ≤ Real.exp ((-163887141961/250000000000 : ℝ)/8) ∧ Real.exp ((-163887141961/250000000000 : ℝ)/8) ≤ (921323946636471183/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-163887141961/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1729_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2076628766069/1000000000000 : ℝ) ≤ 4*Real.exp (15/64 : ℝ)*Real.exp (-mu (radius 8 (1/4 : ℝ))) ∧ (20549/10000 : ℝ) < (2076628766069/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1/4 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1729_exp_radius
  have hrNumeric : (242308308619/250000000000 : ℝ) ≤ Real.exp (-1/32 : ℝ) ∧ Real.exp (-1/32 : ℝ) ≤ (969233234477/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (242308308619/250000000000 : ℝ) ≤ (radius 8 (1/4 : ℝ)) ∧ (radius 8 (1/4 : ℝ)) ≤ (969233234477/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1/4 : ℝ)) (242308308619/250000000000 : ℝ) (969233234477/1000000000000 : ℝ) (246144139043/1000000000000 : ℝ) (30768017381/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1/4 : ℝ)) (242308308619/250000000000 : ℝ) (969233234477/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1/4 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (242308308619/250000000000 : ℝ) (969233234477/1000000000000 : ℝ) (492308308619/500000000000 : ℝ) (984616617239/1000000000000 : ℝ) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1/4 : ℝ)) 1 (492308308619/500000000000 : ℝ) (984616617239/1000000000000 : ℝ) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ) (984556527121/1000000000000 : ℝ) (984556527123/1000000000000 : ℝ) (984556525287/1000000000000 : ℝ) (984556525289/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1/4 : ℝ)) 2 (984556527121/1000000000000 : ℝ) (984556527123/1000000000000 : ℝ) (984556525287/1000000000000 : ℝ) (984556525289/1000000000000 : ℝ) (246139131551/250000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1/4 : ℝ)) 3 (246139131551/250000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1/4 : ℝ)) 4 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1/4 : ℝ)) 5 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1/4 : ℝ)) 6 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1/4 : ℝ)) 7 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1/4 : ℝ))) (246144139043/1000000000000 : ℝ) (30768017381/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1/4 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (246144139043/1000000000000 : ℝ) (30768017381/125000000000 : ℝ) (623072069521/1000000000000 : ℝ) (155768017381/250000000000 : ℝ) (248064577803/500000000000 : ℝ) (124032288903/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1/4 : ℝ))) 1 (623072069521/1000000000000 : ℝ) (155768017381/250000000000 : ℝ) (248064577803/500000000000 : ℝ) (124032288903/250000000000 : ℝ) (559600612563/1000000000000 : ℝ) (69950076571/125000000000 : ℝ) (555989406133/1000000000000 : ℝ) (555989406139/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1/4 : ℝ))) 2 (559600612563/1000000000000 : ℝ) (69950076571/125000000000 : ℝ) (555989406133/1000000000000 : ℝ) (555989406139/1000000000000 : ℝ) (139448752337/250000000000 : ℝ) (278897504677/500000000000 : ℝ) (557792086937/1000000000000 : ℝ) (17431002717/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1/4 : ℝ))) 3 (139448752337/250000000000 : ℝ) (278897504677/500000000000 : ℝ) (557792086937/1000000000000 : ℝ) (17431002717/31250000000 : ℝ) (278896774071/500000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (139448387037/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1/4 : ℝ))) 4 (278896774071/500000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (139448387037/250000000000 : ℝ) (557793548141/1000000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1/4 : ℝ))) 5 (557793548141/1000000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1/4 : ℝ))) 6 (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1/4 : ℝ))) 7 (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1/4 : ℝ)) hmem 8 (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1/4 : ℝ))) hcmem 8 (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1/4 : ℝ)) (984556526203/1000000000000 : ℝ) (492278263103/500000000000 : ℝ) (27889677407/50000000000 : ℝ) (557793548149/1000000000000 : ℝ) (444961783913/500000000000 : ℝ) (222480891961/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1729_exp_lower
  have heNumeric : (2076628766069/1000000000000 : ℝ)/4 ≤ Real.exp (-163887141961/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2076628766069/1000000000000 : ℝ)/4 ≤ Real.exp ((15/64 : ℝ)-(222480891961/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (15/64 : ℝ) (1/4 : ℝ) (222480891961/250000000000 : ℝ) (2076628766069/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1730; no trusted numerical premise.
theorem cover8_leaf1730_exp_radius : (995615110573517933/1000000000000000000 : ℝ) ≤ Real.exp ((-9/256 : ℝ)/8) ∧ Real.exp ((-9/256 : ℝ)/8) ≤ (497807555286758967/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9/256 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1730_exp_lower : (920899455755803651/1000000000000000000 : ℝ) ≤ Real.exp ((-659235337973/1000000000000 : ℝ)/8) ∧ Real.exp ((-659235337973/1000000000000 : ℝ)/8) ≤ (230224863938950913/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-659235337973/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1730_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2068986808891/1000000000000 : ℝ) ≤ 4*Real.exp (1/4 : ℝ)*Real.exp (-mu (radius 8 (9/32 : ℝ))) ∧ (20549/10000 : ℝ) < (2068986808891/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (9/32 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1730_exp_radius
  have hrNumeric : (965454552197/1000000000000 : ℝ) ≤ Real.exp (-9/256 : ℝ) ∧ Real.exp (-9/256 : ℝ) ≤ (482727276099/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (965454552197/1000000000000 : ℝ) ≤ (radius 8 (9/32 : ℝ)) ∧ (radius 8 (9/32 : ℝ)) ≤ (482727276099/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (9/32 : ℝ)) (965454552197/1000000000000 : ℝ) (482727276099/500000000000 : ℝ) (65142875493/250000000000 : ℝ) (260571501977/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (9/32 : ℝ)) (965454552197/1000000000000 : ℝ) (482727276099/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (9/32 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (965454552197/1000000000000 : ℝ) (482727276099/500000000000 : ℝ) (491363638049/500000000000 : ℝ) (982727276099/1000000000000 : ℝ) (982575468957/1000000000000 : ℝ) (491287734479/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (9/32 : ℝ)) 1 (491363638049/500000000000 : ℝ) (982727276099/1000000000000 : ℝ) (982575468957/1000000000000 : ℝ) (491287734479/500000000000 : ℝ) (982651372527/1000000000000 : ℝ) (982651372529/1000000000000 : ℝ) (196530273919/200000000000 : ℝ) (982651369597/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (9/32 : ℝ)) 2 (982651372527/1000000000000 : ℝ) (982651372529/1000000000000 : ℝ) (196530273919/200000000000 : ℝ) (982651369597/1000000000000 : ℝ) (982651371061/1000000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (9/32 : ℝ)) 3 (982651371061/1000000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (9/32 : ℝ)) 4 (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (9/32 : ℝ)) 5 (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (9/32 : ℝ)) 6 (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (9/32 : ℝ)) 7 (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (9/32 : ℝ))) (65142875493/250000000000 : ℝ) (260571501977/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (9/32 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (65142875493/250000000000 : ℝ) (260571501977/1000000000000 : ℝ) (315142875493/500000000000 : ℝ) (630285750989/1000000000000 : ℝ) (510462047533/1000000000000 : ℝ) (510462047539/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (9/32 : ℝ))) 1 (315142875493/500000000000 : ℝ) (630285750989/1000000000000 : ℝ) (510462047533/1000000000000 : ℝ) (510462047539/1000000000000 : ℝ) (570373899259/1000000000000 : ℝ) (557005761/976562500 : ℝ) (7090232663/12500000000 : ℝ) (113443722609/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (9/32 : ℝ))) 2 (570373899259/1000000000000 : ℝ) (557005761/976562500 : ℝ) (7090232663/12500000000 : ℝ) (113443722609/200000000000 : ℝ) (568796256149/1000000000000 : ℝ) (113759251231/200000000000 : ℝ) (142198517057/250000000000 : ℝ) (284397034117/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (9/32 : ℝ))) 3 (568796256149/1000000000000 : ℝ) (113759251231/200000000000 : ℝ) (142198517057/250000000000 : ℝ) (284397034117/500000000000 : ℝ) (142198790547/250000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (284397581097/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (9/32 : ℝ))) 4 (142198790547/250000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (284397581097/500000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (9/32 : ℝ))) 5 (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (9/32 : ℝ))) 6 (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (9/32 : ℝ))) 7 (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (9/32 : ℝ)) hmem 8 (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (9/32 : ℝ))) hcmem 8 (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (9/32 : ℝ)) (49132568553/50000000000 : ℝ) (982651371063/1000000000000 : ℝ) (568795162187/1000000000000 : ℝ) (113759032439/200000000000 : ℝ) (227308834489/250000000000 : ℝ) (909235337973/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1730_exp_lower
  have heNumeric : (2068986808891/1000000000000 : ℝ)/4 ≤ Real.exp (-659235337973/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2068986808891/1000000000000 : ℝ)/4 ≤ Real.exp ((1/4 : ℝ)-(909235337973/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1/4 : ℝ) (9/32 : ℝ) (909235337973/1000000000000 : ℝ) (2068986808891/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1731; no trusted numerical premise.
theorem cover8_leaf1731_exp_radius : (995129089050063087/1000000000000000000 : ℝ) ≤ Real.exp ((-5/128 : ℝ)/8) ∧ Real.exp ((-5/128 : ℝ)/8) ≤ (62195568065628943/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5/128 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1731_exp_lower : (922426071261135607/1000000000000000000 : ℝ) ≤ Real.exp ((-129196873333/200000000000 : ℝ)/8) ∧ Real.exp ((-129196873333/200000000000 : ℝ)/8) ≤ (115303258907641951/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-129196873333/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1731_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1048292671799/500000000000 : ℝ) ≤ 4*Real.exp (9/32 : ℝ)*Real.exp (-mu (radius 8 (5/16 : ℝ))) ∧ (20549/10000 : ℝ) < (1048292671799/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (5/16 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1731_exp_radius
  have hrNumeric : (192338120321/200000000000 : ℝ) ≤ Real.exp (-5/128 : ℝ) ∧ Real.exp (-5/128 : ℝ) ≤ (480845300803/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (192338120321/200000000000 : ℝ) ≤ (radius 8 (5/16 : ℝ)) ∧ (radius 8 (5/16 : ℝ)) ≤ (480845300803/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (5/16 : ℝ)) (192338120321/200000000000 : ℝ) (480845300803/500000000000 : ℝ) (17133572989/62500000000 : ℝ) (68534291957/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (5/16 : ℝ)) (192338120321/200000000000 : ℝ) (480845300803/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (5/16 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (192338120321/200000000000 : ℝ) (480845300803/500000000000 : ℝ) (490422650401/500000000000 : ℝ) (980845300803/1000000000000 : ℝ) (980658249139/1000000000000 : ℝ) (49032912457/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (5/16 : ℝ)) 1 (490422650401/500000000000 : ℝ) (980845300803/1000000000000 : ℝ) (980658249139/1000000000000 : ℝ) (49032912457/50000000000 : ℝ) (98075177497/100000000000 : ℝ) (245187943743/250000000000 : ℝ) (980751770511/1000000000000 : ℝ) (980751770513/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (5/16 : ℝ)) 2 (98075177497/100000000000 : ℝ) (245187943743/250000000000 : ℝ) (980751770511/1000000000000 : ℝ) (980751770513/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (5/16 : ℝ)) 3 (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (5/16 : ℝ)) 4 (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (5/16 : ℝ)) 5 (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (5/16 : ℝ)) 6 (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (5/16 : ℝ)) 7 (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (5/16 : ℝ))) (17133572989/62500000000 : ℝ) (68534291957/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (5/16 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17133572989/62500000000 : ℝ) (68534291957/250000000000 : ℝ) (79633572989/125000000000 : ℝ) (318534291957/500000000000 : ℝ) (523581099567/1000000000000 : ℝ) (130895274893/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (5/16 : ℝ))) 1 (79633572989/125000000000 : ℝ) (318534291957/500000000000 : ℝ) (523581099567/1000000000000 : ℝ) (130895274893/250000000000 : ℝ) (580324841739/1000000000000 : ℝ) (580324841743/1000000000000 : ℝ) (577543998033/1000000000000 : ℝ) (577543998037/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (5/16 : ℝ))) 2 (580324841739/1000000000000 : ℝ) (580324841743/1000000000000 : ℝ) (577543998033/1000000000000 : ℝ) (577543998037/1000000000000 : ℝ) (289467209943/500000000000 : ℝ) (57893441989/100000000000 : ℝ) (578932750201/1000000000000 : ℝ) (289466375103/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (5/16 : ℝ))) 3 (289467209943/500000000000 : ℝ) (57893441989/100000000000 : ℝ) (578932750201/1000000000000 : ℝ) (289466375103/500000000000 : ℝ) (578933585043/1000000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (5/16 : ℝ))) 4 (578933585043/1000000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (5/16 : ℝ))) 5 (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (5/16 : ℝ))) 6 (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (5/16 : ℝ))) 7 (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (5/16 : ℝ)) hmem 8 (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (5/16 : ℝ))) hcmem 8 (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (5/16 : ℝ)) (49037588637/50000000000 : ℝ) (980751772743/1000000000000 : ℝ) (289466792521/500000000000 : ℝ) (72366698131/125000000000 : ℝ) (927234366651/1000000000000 : ℝ) (185446873333/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1731_exp_lower
  have heNumeric : (1048292671799/500000000000 : ℝ)/4 ≤ Real.exp (-129196873333/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1048292671799/500000000000 : ℝ)/4 ≤ Real.exp ((9/32 : ℝ)-(185446873333/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (9/32 : ℝ) (5/16 : ℝ) (185446873333/200000000000 : ℝ) (1048292671799/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1732; no trusted numerical premise.
theorem cover8_leaf1732_exp_radius : (497078878829568921/500000000000000000 : ℝ) ≤ Real.exp ((-3/64 : ℝ)/8) ∧ Real.exp ((-3/64 : ℝ)/8) ≤ (994157757659137843/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/64 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1732_exp_lower : (3602488675486223/3906250000000000 : ℝ) ≤ Real.exp ((-12952468661/20000000000 : ℝ)/8) ∧ Real.exp ((-12952468661/20000000000 : ℝ)/8) ≤ (922237100924473089/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-12952468661/20000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1732_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1046575857889/500000000000 : ℝ) ≤ 4*Real.exp (5/16 : ℝ)*Real.exp (-mu (radius 8 (3/8 : ℝ))) ∧ (20549/10000 : ℝ) < (1046575857889/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (3/8 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1732_exp_radius
  have hrNumeric : (954206665969/1000000000000 : ℝ) ≤ Real.exp (-3/64 : ℝ) ∧ Real.exp (-3/64 : ℝ) ≤ (95420666597/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (954206665969/1000000000000 : ℝ) ≤ (radius 8 (3/8 : ℝ)) ∧ (radius 8 (3/8 : ℝ)) ≤ (95420666597/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (3/8 : ℝ)) (954206665969/1000000000000 : ℝ) (95420666597/100000000000 : ℝ) (37393523549/125000000000 : ℝ) (74787047099/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (3/8 : ℝ)) (954206665969/1000000000000 : ℝ) (95420666597/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (3/8 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (954206665969/1000000000000 : ℝ) (95420666597/100000000000 : ℝ) (122137916623/125000000000 : ℝ) (195420666597/200000000000 : ℝ) (976835024949/1000000000000 : ℝ) (976835024951/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (3/8 : ℝ)) 1 (122137916623/125000000000 : ℝ) (195420666597/200000000000 : ℝ) (976835024949/1000000000000 : ℝ) (976835024951/1000000000000 : ℝ) (488484589483/500000000000 : ℝ) (122121147371/125000000000 : ℝ) (195393833951/200000000000 : ℝ) (488484584879/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (3/8 : ℝ)) 2 (488484589483/500000000000 : ℝ) (122121147371/125000000000 : ℝ) (195393833951/200000000000 : ℝ) (488484584879/500000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (3/8 : ℝ)) 3 (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (3/8 : ℝ)) 4 (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (3/8 : ℝ)) 5 (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (3/8 : ℝ)) 6 (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (3/8 : ℝ)) 7 (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (3/8 : ℝ))) (37393523549/125000000000 : ℝ) (74787047099/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (3/8 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (37393523549/125000000000 : ℝ) (74787047099/250000000000 : ℝ) (162393523549/250000000000 : ℝ) (324787047099/500000000000 : ℝ) (68368051337/125000000000 : ℝ) (546944410701/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (3/8 : ℝ))) 1 (162393523549/250000000000 : ℝ) (324787047099/500000000000 : ℝ) (68368051337/125000000000 : ℝ) (546944410701/1000000000000 : ℝ) (299129626223/500000000000 : ℝ) (11965185049/20000000000 : ℝ) (596054460727/1000000000000 : ℝ) (149013615183/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (3/8 : ℝ))) 2 (299129626223/500000000000 : ℝ) (11965185049/20000000000 : ℝ) (596054460727/1000000000000 : ℝ) (149013615183/250000000000 : ℝ) (298578428293/500000000000 : ℝ) (597156856591/1000000000000 : ℝ) (597155839033/1000000000000 : ℝ) (298577919519/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (3/8 : ℝ))) 3 (298578428293/500000000000 : ℝ) (597156856591/1000000000000 : ℝ) (597155839033/1000000000000 : ℝ) (298577919519/500000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (3/8 : ℝ))) 4 (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (3/8 : ℝ))) 5 (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (3/8 : ℝ))) 6 (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (3/8 : ℝ))) 7 (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (3/8 : ℝ)) hmem 8 (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (3/8 : ℝ))) hcmem 8 (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (3/8 : ℝ)) (24424229359/25000000000 : ℝ) (976969174363/1000000000000 : ℝ) (597156347809/1000000000000 : ℝ) (119431269563/200000000000 : ℝ) (240030858259/250000000000 : ℝ) (19202468661/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1732_exp_lower
  have heNumeric : (1046575857889/500000000000 : ℝ)/4 ≤ Real.exp (-12952468661/20000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1046575857889/500000000000 : ℝ)/4 ≤ Real.exp ((5/16 : ℝ)-(19202468661/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (5/16 : ℝ) (3/8 : ℝ) (19202468661/20000000000 : ℝ) (1046575857889/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1733; no trusted numerical premise.
theorem cover8_leaf1733_exp_radius : (124027242282530439/125000000000000000 : ℝ) ≤ Real.exp ((-1/16 : ℝ)/8) ∧ Real.exp ((-1/16 : ℝ)/8) ≤ (992217938260243513/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/16 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1733_exp_lower : (184576146007248227/200000000000000000 : ℝ) ≤ Real.exp ((-642042181797/1000000000000 : ℝ)/8) ∧ Real.exp ((-642042181797/1000000000000 : ℝ)/8) ≤ (57680045627265071/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-642042181797/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1733_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (526216695843/250000000000 : ℝ) ≤ 4*Real.exp (3/8 : ℝ)*Real.exp (-mu (radius 8 (1/2 : ℝ))) ∧ (20549/10000 : ℝ) < (526216695843/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1/2 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1733_exp_radius
  have hrNumeric : (939413062813/1000000000000 : ℝ) ≤ Real.exp (-1/16 : ℝ) ∧ Real.exp (-1/16 : ℝ) ≤ (469706531407/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (939413062813/1000000000000 : ℝ) ≤ (radius 8 (1/2 : ℝ)) ∧ (radius 8 (1/2 : ℝ)) ≤ (469706531407/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1/2 : ℝ)) (939413062813/1000000000000 : ℝ) (469706531407/500000000000 : ℝ) (342787248033/1000000000000 : ℝ) (342787248037/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1/2 : ℝ)) (939413062813/1000000000000 : ℝ) (469706531407/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1/2 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (939413062813/1000000000000 : ℝ) (469706531407/500000000000 : ℝ) (484853265703/500000000000 : ℝ) (969706531407/1000000000000 : ℝ) (242308308619/250000000000 : ℝ) (969233234477/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1/2 : ℝ)) 1 (484853265703/500000000000 : ℝ) (969706531407/1000000000000 : ℝ) (242308308619/250000000000 : ℝ) (969233234477/1000000000000 : ℝ) (969469882941/1000000000000 : ℝ) (484734941471/500000000000 : ℝ) (969469854057/1000000000000 : ℝ) (969469854059/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1/2 : ℝ)) 2 (969469882941/1000000000000 : ℝ) (484734941471/500000000000 : ℝ) (969469854057/1000000000000 : ℝ) (969469854059/1000000000000 : ℝ) (969469868499/1000000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1/2 : ℝ)) 3 (969469868499/1000000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1/2 : ℝ)) 4 (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1/2 : ℝ)) 5 (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1/2 : ℝ)) 6 (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1/2 : ℝ)) 7 (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1/2 : ℝ))) (342787248033/1000000000000 : ℝ) (342787248037/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1/2 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (342787248033/1000000000000 : ℝ) (342787248037/1000000000000 : ℝ) (41962101501/62500000000 : ℝ) (671393624019/1000000000000 : ℝ) (292740178329/500000000000 : ℝ) (292740178331/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1/2 : ℝ))) 1 (41962101501/62500000000 : ℝ) (671393624019/1000000000000 : ℝ) (292740178329/500000000000 : ℝ) (292740178331/500000000000 : ℝ) (628436990337/1000000000000 : ℝ) (628436990341/1000000000000 : ℝ) (313483563543/500000000000 : ℝ) (62696712709/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1/2 : ℝ))) 2 (628436990337/1000000000000 : ℝ) (628436990341/1000000000000 : ℝ) (313483563543/500000000000 : ℝ) (62696712709/100000000000 : ℝ) (627702058711/1000000000000 : ℝ) (156925514679/250000000000 : ℝ) (627701628471/1000000000000 : ℝ) (156925407119/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1/2 : ℝ))) 3 (627702058711/1000000000000 : ℝ) (156925514679/250000000000 : ℝ) (627701628471/1000000000000 : ℝ) (156925407119/250000000000 : ℝ) (627701843591/1000000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1/2 : ℝ))) 4 (627701843591/1000000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1/2 : ℝ))) 5 (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1/2 : ℝ))) 6 (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1/2 : ℝ))) 7 (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1/2 : ℝ)) hmem 8 (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1/2 : ℝ))) hcmem 8 (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1/2 : ℝ)) (484734934249/500000000000 : ℝ) (969469868501/1000000000000 : ℝ) (62770184359/100000000000 : ℝ) (156925460899/250000000000 : ℝ) (1017042181783/1000000000000 : ℝ) (1017042181797/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1733_exp_lower
  have heNumeric : (526216695843/250000000000 : ℝ)/4 ≤ Real.exp (-642042181797/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (526216695843/250000000000 : ℝ)/4 ≤ Real.exp ((3/8 : ℝ)-(1017042181797/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (3/8 : ℝ) (1/2 : ℝ) (1017042181797/1000000000000 : ℝ) (526216695843/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1734; no trusted numerical premise.
theorem cover8_leaf1734_exp_radius : (988349647113845047/1000000000000000000 : ℝ) ≤ Real.exp ((-3/32 : ℝ)/8) ∧ Real.exp ((-3/32 : ℝ)/8) ≤ (123543705889230631/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3/32 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1734_exp_lower : (231653219638557581/250000000000000000 : ℝ) ≤ Real.exp ((-609755259007/1000000000000 : ℝ)/8) ∧ Real.exp ((-609755259007/1000000000000 : ℝ)/8) ≤ (37064515142169213/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-609755259007/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1734_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2173935462319/1000000000000 : ℝ) ≤ 4*Real.exp (1/2 : ℝ)*Real.exp (-mu (radius 8 (3/4 : ℝ))) ∧ (20549/10000 : ℝ) < (2173935462319/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (3/4 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1734_exp_radius
  have hrNumeric : (45525518069/50000000000 : ℝ) ≤ Real.exp (-3/32 : ℝ) ∧ Real.exp (-3/32 : ℝ) ≤ (910510361381/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (45525518069/50000000000 : ℝ) ≤ (radius 8 (3/4 : ℝ)) ∧ (radius 8 (3/4 : ℝ)) ≤ (910510361381/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (3/4 : ℝ)) (45525518069/50000000000 : ℝ) (910510361381/1000000000000 : ℝ) (413486253481/1000000000000 : ℝ) (103371563371/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (3/4 : ℝ)) (45525518069/50000000000 : ℝ) (910510361381/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (3/4 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (45525518069/50000000000 : ℝ) (910510361381/1000000000000 : ℝ) (95525518069/100000000000 : ℝ) (955255180691/1000000000000 : ℝ) (954206665969/1000000000000 : ℝ) (95420666597/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (3/4 : ℝ)) 1 (95525518069/100000000000 : ℝ) (955255180691/1000000000000 : ℝ) (954206665969/1000000000000 : ℝ) (95420666597/100000000000 : ℝ) (954730923329/1000000000000 : ℝ) (954730923331/1000000000000 : ℝ) (95473077939/100000000000 : ℝ) (3729417107/3906250000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (3/4 : ℝ)) 2 (954730923329/1000000000000 : ℝ) (954730923331/1000000000000 : ℝ) (95473077939/100000000000 : ℝ) (3729417107/3906250000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (3/4 : ℝ)) 3 (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (3/4 : ℝ)) 4 (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (3/4 : ℝ)) 5 (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (3/4 : ℝ)) 6 (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (3/4 : ℝ)) 7 (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (3/4 : ℝ))) (413486253481/1000000000000 : ℝ) (103371563371/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (3/4 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (413486253481/1000000000000 : ℝ) (103371563371/250000000000 : ℝ) (35337156337/50000000000 : ℝ) (353371563371/500000000000 : ℝ) (643028967839/1000000000000 : ℝ) (643028967843/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (3/4 : ℝ))) 1 (35337156337/50000000000 : ℝ) (353371563371/500000000000 : ℝ) (643028967839/1000000000000 : ℝ) (643028967843/1000000000000 : ℝ) (674886047289/1000000000000 : ℝ) (674886047293/1000000000000 : ℝ) (337066871449/500000000000 : ℝ) (337066871451/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (3/4 : ℝ))) 2 (674886047289/1000000000000 : ℝ) (674886047293/1000000000000 : ℝ) (337066871449/500000000000 : ℝ) (337066871451/500000000000 : ℝ) (674509895093/1000000000000 : ℝ) (337254947549/500000000000 : ℝ) (674509790209/1000000000000 : ℝ) (337254895107/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (3/4 : ℝ))) 3 (674509895093/1000000000000 : ℝ) (337254947549/500000000000 : ℝ) (674509790209/1000000000000 : ℝ) (337254895107/500000000000 : ℝ) (674509842651/1000000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (3/4 : ℝ))) 4 (674509842651/1000000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (3/4 : ℝ))) 5 (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (3/4 : ℝ))) 6 (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (3/4 : ℝ))) 7 (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (3/4 : ℝ)) hmem 8 (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (3/4 : ℝ))) hcmem 8 (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (3/4 : ℝ)) (954730851359/1000000000000 : ℝ) (477365425681/500000000000 : ℝ) (13490196853/20000000000 : ℝ) (21078432583/31250000000 : ℝ) (69359703687/62500000000 : ℝ) (1109755259007/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1734_exp_lower
  have heNumeric : (2173935462319/1000000000000 : ℝ)/4 ≤ Real.exp (-609755259007/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2173935462319/1000000000000 : ℝ)/4 ≤ Real.exp ((1/2 : ℝ)-(1109755259007/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1/2 : ℝ) (3/4 : ℝ) (1109755259007/1000000000000 : ℝ) (2173935462319/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1735; no trusted numerical premise.
theorem cover8_leaf1735_exp_radius : (196899287401081681/200000000000000000 : ℝ) ≤ Real.exp ((-1/8 : ℝ)/8) ∧ Real.exp ((-1/8 : ℝ)/8) ≤ (492248218502704203/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/8 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1735_exp_lower : (236725532789877147/250000000000000000 : ℝ) ≤ Real.exp ((-436476298601/1000000000000 : ℝ)/8) ∧ Real.exp ((-436476298601/1000000000000 : ℝ)/8) ≤ (946902131159508589/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-436476298601/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1735_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1292619632303/500000000000 : ℝ) ≤ 4*Real.exp (3/4 : ℝ)*Real.exp (-mu (radius 8 (1/1 : ℝ))) ∧ (20549/10000 : ℝ) < (1292619632303/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1/1 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1735_exp_radius
  have hrNumeric : (110312112823/125000000000 : ℝ) ≤ Real.exp (-1/8 : ℝ) ∧ Real.exp (-1/8 : ℝ) ≤ (176499380517/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (110312112823/125000000000 : ℝ) ≤ (radius 8 (1/1 : ℝ)) ∧ (radius 8 (1/1 : ℝ)) ≤ (176499380517/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1/1 : ℝ)) (110312112823/125000000000 : ℝ) (176499380517/200000000000 : ℝ) (470318208161/1000000000000 : ℝ) (470318208163/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1/1 : ℝ)) (110312112823/125000000000 : ℝ) (176499380517/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1/1 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (110312112823/125000000000 : ℝ) (176499380517/200000000000 : ℝ) (235312112823/250000000000 : ℝ) (941248451293/1000000000000 : ℝ) (939413062813/1000000000000 : ℝ) (469706531407/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1/1 : ℝ)) 1 (235312112823/250000000000 : ℝ) (941248451293/1000000000000 : ℝ) (939413062813/1000000000000 : ℝ) (469706531407/500000000000 : ℝ) (235082689263/250000000000 : ℝ) (470165378527/500000000000 : ℝ) (940330309251/1000000000000 : ℝ) (940330309253/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1/1 : ℝ)) 2 (235082689263/250000000000 : ℝ) (470165378527/500000000000 : ℝ) (940330309251/1000000000000 : ℝ) (940330309253/1000000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1/1 : ℝ)) 3 (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1/1 : ℝ)) 4 (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1/1 : ℝ)) 5 (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1/1 : ℝ)) 6 (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1/1 : ℝ)) 7 (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1/1 : ℝ))) (470318208161/1000000000000 : ℝ) (470318208163/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1/1 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (470318208161/1000000000000 : ℝ) (470318208163/1000000000000 : ℝ) (9189488801/12500000000 : ℝ) (367579552041/500000000000 : ℝ) (27431899917/40000000000 : ℝ) (85724687241/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1/1 : ℝ))) 1 (9189488801/12500000000 : ℝ) (367579552041/500000000000 : ℝ) (27431899917/40000000000 : ℝ) (85724687241/125000000000 : ℝ) (355239150501/500000000000 : ℝ) (142095660201/200000000000 : ℝ) (177512371779/250000000000 : ℝ) (8875618589/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1/1 : ℝ))) 2 (355239150501/500000000000 : ℝ) (142095660201/200000000000 : ℝ) (177512371779/250000000000 : ℝ) (8875618589/12500000000 : ℝ) (710263894059/1000000000000 : ℝ) (710263894063/1000000000000 : ℝ) (710263861697/1000000000000 : ℝ) (355131930851/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1/1 : ℝ))) 3 (710263894059/1000000000000 : ℝ) (710263894063/1000000000000 : ℝ) (710263861697/1000000000000 : ℝ) (355131930851/500000000000 : ℝ) (355131938939/500000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1/1 : ℝ))) 4 (355131938939/500000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1/1 : ℝ))) 5 (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1/1 : ℝ))) 6 (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1/1 : ℝ))) 7 (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1/1 : ℝ)) hmem 8 (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1/1 : ℝ))) hcmem 8 (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1/1 : ℝ)) (940330533151/1000000000000 : ℝ) (470165266577/500000000000 : ℝ) (710263877877/1000000000000 : ℝ) (710263877883/1000000000000 : ℝ) (593238149293/500000000000 : ℝ) (1186476298601/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1735_exp_lower
  have heNumeric : (1292619632303/500000000000 : ℝ)/4 ≤ Real.exp (-436476298601/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1292619632303/500000000000 : ℝ)/4 ≤ Real.exp ((3/4 : ℝ)-(1186476298601/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (3/4 : ℝ) (1/1 : ℝ) (1186476298601/1000000000000 : ℝ) (1292619632303/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1725_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1725_certificate
#check SmaleRate.Proofs.cover8_leaf1726_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1726_certificate
#check SmaleRate.Proofs.cover8_leaf1727_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1727_certificate
#check SmaleRate.Proofs.cover8_leaf1728_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1728_certificate
#check SmaleRate.Proofs.cover8_leaf1729_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1729_certificate
#check SmaleRate.Proofs.cover8_leaf1730_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1730_certificate
#check SmaleRate.Proofs.cover8_leaf1731_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1731_certificate
#check SmaleRate.Proofs.cover8_leaf1732_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1732_certificate
#check SmaleRate.Proofs.cover8_leaf1733_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1733_certificate
#check SmaleRate.Proofs.cover8_leaf1734_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1734_certificate
#check SmaleRate.Proofs.cover8_leaf1735_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1735_certificate
