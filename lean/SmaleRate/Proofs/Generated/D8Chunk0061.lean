/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1525; no trusted numerical premise.
theorem cover8_leaf1525_exp_radius : (498983583218979303/500000000000000000 : ℝ) ≤ Real.exp ((-8535/524288 : ℝ)/8) ∧ Real.exp ((-8535/524288 : ℝ)/8) ≤ (997967166437958607/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8535/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1525_exp_lower : (920113905632613099/1000000000000000000 : ℝ) ≤ Real.exp ((-5328499592493/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328499592493/8000000000000 : ℝ)/8) ≤ (9201139056326131/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328499592493/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1525_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054909713729/1000000000000 : ℝ) ≤ 4*Real.exp (4267/32768 : ℝ)*Real.exp (-mu (radius 8 (8535/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054909713729/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8535/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1525_exp_radius
  have hrNumeric : (245963142453/250000000000 : ℝ) ≤ Real.exp (-8535/524288 : ℝ) ∧ Real.exp (-8535/524288 : ℝ) ≤ (983852569813/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245963142453/250000000000 : ℝ) ≤ (radius 8 (8535/65536 : ℝ)) ∧ (radius 8 (8535/65536 : ℝ)) ≤ (983852569813/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8535/65536 : ℝ)) (245963142453/250000000000 : ℝ) (983852569813/1000000000000 : ℝ) (22372597941/125000000000 : ℝ) (89490391767/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8535/65536 : ℝ)) (245963142453/250000000000 : ℝ) (983852569813/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8535/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245963142453/250000000000 : ℝ) (983852569813/1000000000000 : ℝ) (495963142453/500000000000 : ℝ) (991926284907/1000000000000 : ℝ) (12398667833/12500000000 : ℝ) (991893426641/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8535/65536 : ℝ)) 1 (495963142453/500000000000 : ℝ) (991926284907/1000000000000 : ℝ) (12398667833/12500000000 : ℝ) (991893426641/1000000000000 : ℝ) (991909855773/1000000000000 : ℝ) (495954927887/500000000000 : ℝ) (247977463909/250000000000 : ℝ) (495954927819/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8535/65536 : ℝ)) 2 (991909855773/1000000000000 : ℝ) (495954927887/500000000000 : ℝ) (247977463909/250000000000 : ℝ) (495954927819/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8535/65536 : ℝ)) 3 (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8535/65536 : ℝ)) 4 (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8535/65536 : ℝ)) 5 (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8535/65536 : ℝ)) 6 (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8535/65536 : ℝ)) 7 (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8535/65536 : ℝ))) (22372597941/125000000000 : ℝ) (89490391767/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8535/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22372597941/125000000000 : ℝ) (89490391767/500000000000 : ℝ) (147372597941/250000000000 : ℝ) (589490391767/1000000000000 : ℝ) (84612241083/200000000000 : ℝ) (26441325339/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8535/65536 : ℝ))) 1 (147372597941/250000000000 : ℝ) (589490391767/1000000000000 : ℝ) (84612241083/200000000000 : ℝ) (26441325339/62500000000 : ℝ) (506275798589/1000000000000 : ℝ) (126568949649/250000000000 : ℝ) (99878028759/200000000000 : ℝ) (499390143803/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8535/65536 : ℝ))) 2 (506275798589/1000000000000 : ℝ) (126568949649/250000000000 : ℝ) (99878028759/200000000000 : ℝ) (499390143803/1000000000000 : ℝ) (62854121399/125000000000 : ℝ) (314270607/625000000 : ℝ) (502821184773/1000000000000 : ℝ) (251410592391/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8535/65536 : ℝ))) 3 (62854121399/125000000000 : ℝ) (314270607/625000000 : ℝ) (502821184773/1000000000000 : ℝ) (251410592391/500000000000 : ℝ) (251413538991/500000000000 : ℝ) (502827077991/1000000000000 : ℝ) (502827077947/1000000000000 : ℝ) (502827077957/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8535/65536 : ℝ))) 4 (251413538991/500000000000 : ℝ) (502827077991/1000000000000 : ℝ) (502827077947/1000000000000 : ℝ) (502827077957/1000000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8535/65536 : ℝ))) 5 (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8535/65536 : ℝ))) 6 (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8535/65536 : ℝ))) 7 (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8535/65536 : ℝ)) hmem 8 (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8535/65536 : ℝ))) hcmem 8 (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8535/65536 : ℝ)) (123988731963/125000000000 : ℝ) (495954927853/500000000000 : ℝ) (125706769491/250000000000 : ℝ) (251413538987/500000000000 : ℝ) (398140477451/500000000000 : ℝ) (796280954921/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1525_exp_lower
  have heNumeric : (2054909713729/1000000000000 : ℝ)/4 ≤ Real.exp (-5328499592493/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054909713729/1000000000000 : ℝ)/4 ≤ Real.exp ((4267/32768 : ℝ)-(796280954921/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4267/32768 : ℝ) (8535/65536 : ℝ) (796280954921/1000000000000 : ℝ) (2054909713729/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1526; no trusted numerical premise.
theorem cover8_leaf1526_exp_radius : (498983464252036579/500000000000000000 : ℝ) ≤ Real.exp ((-1067/65536 : ℝ)/8) ∧ Real.exp ((-1067/65536 : ℝ)/8) ≤ (997966928504073159/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1067/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1526_exp_lower : (920113929244468623/1000000000000000000 : ℝ) ≤ Real.exp ((-2131399180053/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131399180053/3200000000000 : ℝ)/8) ≤ (57507120577779289/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131399180053/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1526_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863766949/125000000000 : ℝ) ≤ 4*Real.exp (8535/65536 : ℝ)*Real.exp (-mu (radius 8 (1067/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256863766949/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1067/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1526_exp_radius
  have hrNumeric : (61490668329/62500000000 : ℝ) ≤ Real.exp (-1067/65536 : ℝ) ∧ Real.exp (-1067/65536 : ℝ) ≤ (196770138653/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61490668329/62500000000 : ℝ) ≤ (radius 8 (1067/8192 : ℝ)) ∧ (radius 8 (1067/8192 : ℝ)) ≤ (196770138653/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1067/8192 : ℝ)) (61490668329/62500000000 : ℝ) (196770138653/200000000000 : ℝ) (35798219711/200000000000 : ℝ) (178991098561/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1067/8192 : ℝ)) (61490668329/62500000000 : ℝ) (196770138653/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1067/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61490668329/62500000000 : ℝ) (196770138653/200000000000 : ℝ) (123990668329/125000000000 : ℝ) (991925346633/1000000000000 : ℝ) (991892480697/1000000000000 : ℝ) (495946240349/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1067/8192 : ℝ)) 1 (123990668329/125000000000 : ℝ) (991925346633/1000000000000 : ℝ) (991892480697/1000000000000 : ℝ) (495946240349/500000000000 : ℝ) (1937322097/1953125000 : ℝ) (495954456833/500000000000 : ℝ) (123988614191/125000000000 : ℝ) (99190891353/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1067/8192 : ℝ)) 2 (1937322097/1953125000 : ℝ) (495954456833/500000000000 : ℝ) (123988614191/125000000000 : ℝ) (99190891353/100000000000 : ℝ) (247977228399/250000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1067/8192 : ℝ)) 3 (247977228399/250000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1067/8192 : ℝ)) 4 (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1067/8192 : ℝ)) 5 (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1067/8192 : ℝ)) 6 (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1067/8192 : ℝ)) 7 (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1067/8192 : ℝ))) (35798219711/200000000000 : ℝ) (178991098561/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1067/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35798219711/200000000000 : ℝ) (178991098561/1000000000000 : ℝ) (589495549277/1000000000000 : ℝ) (589495549281/1000000000000 : ℝ) (423073396179/1000000000000 : ℝ) (423073396187/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1067/8192 : ℝ))) 1 (589495549277/1000000000000 : ℝ) (589495549281/1000000000000 : ℝ) (423073396179/1000000000000 : ℝ) (423073396187/1000000000000 : ℝ) (63285559091/125000000000 : ℝ) (253142236367/500000000000 : ℝ) (124849880873/250000000000 : ℝ) (998799047/2000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1067/8192 : ℝ))) 2 (63285559091/125000000000 : ℝ) (253142236367/500000000000 : ℝ) (124849880873/250000000000 : ℝ) (998799047/2000000000 : ℝ) (50284199811/100000000000 : ℝ) (502841998117/1000000000000 : ℝ) (251415107159/500000000000 : ℝ) (251415107163/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1067/8192 : ℝ))) 3 (50284199811/100000000000 : ℝ) (502841998117/1000000000000 : ℝ) (251415107159/500000000000 : ℝ) (251415107163/500000000000 : ℝ) (251418053107/500000000000 : ℝ) (251418053111/500000000000 : ℝ) (502836106179/1000000000000 : ℝ) (502836106187/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1067/8192 : ℝ))) 4 (251418053107/500000000000 : ℝ) (251418053111/500000000000 : ℝ) (502836106179/1000000000000 : ℝ) (502836106187/1000000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1067/8192 : ℝ))) 5 (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1067/8192 : ℝ))) 6 (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1067/8192 : ℝ))) 7 (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1067/8192 : ℝ)) hmem 8 (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1067/8192 : ℝ))) hcmem 8 (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1067/8192 : ℝ)) (198381782719/200000000000 : ℝ) (495954456799/500000000000 : ℝ) (125709026549/250000000000 : ℝ) (100567221241/200000000000 : ℝ) (398148004199/500000000000 : ℝ) (159259201683/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1526_exp_lower
  have heNumeric : (256863766949/125000000000 : ℝ)/4 ≤ Real.exp (-2131399180053/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863766949/125000000000 : ℝ)/4 ≤ Real.exp ((8535/65536 : ℝ)-(159259201683/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8535/65536 : ℝ) (1067/8192 : ℝ) (159259201683/200000000000 : ℝ) (256863766949/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1527; no trusted numerical premise.
theorem cover8_leaf1527_exp_radius : (997966690570244437/1000000000000000000 : ℝ) ≤ Real.exp ((-8537/524288 : ℝ)/8) ∧ Real.exp ((-8537/524288 : ℝ)/8) ≤ (498983345285122219/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8537/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1527_exp_lower : (230028488248470447/250000000000000000 : ℝ) ≤ Real.exp ((-1332124074551/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332124074551/2000000000000 : ℝ)/8) ≤ (920113952993881789/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332124074551/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1527_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054910559913/1000000000000 : ℝ) ≤ 4*Real.exp (1067/8192 : ℝ)*Real.exp (-mu (radius 8 (8537/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054910559913/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8537/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1527_exp_radius
  have hrNumeric : (12298110209/12500000000 : ℝ) ≤ Real.exp (-8537/524288 : ℝ) ∧ Real.exp (-8537/524288 : ℝ) ≤ (983848816721/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (12298110209/12500000000 : ℝ) ≤ (radius 8 (8537/65536 : ℝ)) ∧ (radius 8 (8537/65536 : ℝ)) ≤ (983848816721/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8537/65536 : ℝ)) (12298110209/12500000000 : ℝ) (983848816721/1000000000000 : ℝ) (89500706473/500000000000 : ℝ) (22375176619/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8537/65536 : ℝ)) (12298110209/12500000000 : ℝ) (983848816721/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8537/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (12298110209/12500000000 : ℝ) (983848816721/1000000000000 : ℝ) (24798110209/25000000000 : ℝ) (991924408361/1000000000000 : ℝ) (198378306951/200000000000 : ℝ) (991891534757/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8537/65536 : ℝ)) 1 (24798110209/25000000000 : ℝ) (991924408361/1000000000000 : ℝ) (198378306951/200000000000 : ℝ) (991891534757/1000000000000 : ℝ) (991907971557/1000000000000 : ℝ) (991907971559/1000000000000 : ℝ) (991907971421/1000000000000 : ℝ) (991907971423/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8537/65536 : ℝ)) 2 (991907971557/1000000000000 : ℝ) (991907971559/1000000000000 : ℝ) (991907971421/1000000000000 : ℝ) (991907971423/1000000000000 : ℝ) (991907971489/1000000000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8537/65536 : ℝ)) 3 (991907971489/1000000000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8537/65536 : ℝ)) 4 (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8537/65536 : ℝ)) 5 (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8537/65536 : ℝ)) 6 (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8537/65536 : ℝ)) 7 (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8537/65536 : ℝ))) (89500706473/500000000000 : ℝ) (22375176619/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8537/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89500706473/500000000000 : ℝ) (22375176619/125000000000 : ℝ) (589500706473/1000000000000 : ℝ) (147375176619/250000000000 : ℝ) (5288569823/12500000000 : ℝ) (52885698231/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8537/65536 : ℝ))) 1 (589500706473/1000000000000 : ℝ) (147375176619/250000000000 : ℝ) (5288569823/12500000000 : ℝ) (52885698231/125000000000 : ℝ) (126573286539/250000000000 : ℝ) (253146573081/500000000000 : ℝ) (249704451177/500000000000 : ℝ) (499408902361/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8537/65536 : ℝ))) 2 (126573286539/250000000000 : ℝ) (253146573081/500000000000 : ℝ) (249704451177/500000000000 : ℝ) (499408902361/1000000000000 : ℝ) (100570204851/200000000000 : ℝ) (251425512131/500000000000 : ℝ) (502839243089/1000000000000 : ℝ) (502839243097/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8537/65536 : ℝ))) 3 (100570204851/200000000000 : ℝ) (251425512131/500000000000 : ℝ) (502839243089/1000000000000 : ℝ) (502839243097/1000000000000 : ℝ) (62855641709/125000000000 : ℝ) (6285564171/12500000000 : ℝ) (502845133637/1000000000000 : ℝ) (100569026729/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8537/65536 : ℝ))) 4 (62855641709/125000000000 : ℝ) (6285564171/12500000000 : ℝ) (502845133637/1000000000000 : ℝ) (100569026729/200000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8537/65536 : ℝ))) 5 (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8537/65536 : ℝ))) 6 (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8537/65536 : ℝ))) 7 (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8537/65536 : ℝ)) hmem 8 (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8537/65536 : ℝ))) hcmem 8 (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8537/65536 : ℝ)) (30997124109/31250000000 : ℝ) (991907971491/1000000000000 : ℝ) (251422566827/500000000000 : ℝ) (502845133663/1000000000000 : ℝ) (159262212139/200000000000 : ℝ) (796311060713/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1527_exp_lower
  have heNumeric : (2054910559913/1000000000000 : ℝ)/4 ≤ Real.exp (-1332124074551/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054910559913/1000000000000 : ℝ)/4 ≤ Real.exp ((1067/8192 : ℝ)-(796311060713/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1067/8192 : ℝ) (8537/65536 : ℝ) (796311060713/1000000000000 : ℝ) (2054910559913/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1528; no trusted numerical premise.
theorem cover8_leaf1528_exp_radius : (199593290527294489/200000000000000000 : ℝ) ≤ Real.exp ((-4269/262144 : ℝ)/8) ∧ Real.exp ((-4269/262144 : ℝ)/8) ≤ (498983226318236223/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4269/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1528_exp_lower : (460056988440023753/500000000000000000 : ℝ) ≤ Real.exp ((-10656989273527/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656989273527/16000000000000 : ℝ)/8) ≤ (920113976880047507/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656989273527/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1528_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054910986677/1000000000000 : ℝ) ≤ 4*Real.exp (8537/65536 : ℝ)*Real.exp (-mu (radius 8 (4269/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054910986677/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4269/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1528_exp_radius
  have hrNumeric : (983846940179/1000000000000 : ℝ) ≤ Real.exp (-4269/262144 : ℝ) ∧ Real.exp (-4269/262144 : ℝ) ≤ (49192347009/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983846940179/1000000000000 : ℝ) ≤ (radius 8 (4269/32768 : ℝ)) ∧ (radius 8 (4269/32768 : ℝ)) ≤ (49192347009/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4269/32768 : ℝ)) (983846940179/1000000000000 : ℝ) (49192347009/50000000000 : ℝ) (89505863353/500000000000 : ℝ) (179011726713/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4269/32768 : ℝ)) (983846940179/1000000000000 : ℝ) (49192347009/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4269/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983846940179/1000000000000 : ℝ) (49192347009/50000000000 : ℝ) (991923470089/1000000000000 : ℝ) (99192347009/100000000000 : ℝ) (495945294407/500000000000 : ℝ) (61993161801/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4269/32768 : ℝ)) 1 (991923470089/1000000000000 : ℝ) (99192347009/100000000000 : ℝ) (495945294407/500000000000 : ℝ) (61993161801/62500000000 : ℝ) (991907029451/1000000000000 : ℝ) (991907029453/1000000000000 : ℝ) (198381405863/200000000000 : ℝ) (991907029317/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4269/32768 : ℝ)) 2 (991907029451/1000000000000 : ℝ) (991907029453/1000000000000 : ℝ) (198381405863/200000000000 : ℝ) (991907029317/1000000000000 : ℝ) (991907029383/1000000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4269/32768 : ℝ)) 3 (991907029383/1000000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4269/32768 : ℝ)) 4 (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4269/32768 : ℝ)) 5 (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4269/32768 : ℝ)) 6 (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4269/32768 : ℝ)) 7 (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4269/32768 : ℝ))) (89505863353/500000000000 : ℝ) (179011726713/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4269/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89505863353/500000000000 : ℝ) (179011726713/1000000000000 : ℝ) (589505863353/1000000000000 : ℝ) (589505863357/1000000000000 : ℝ) (105774443601/250000000000 : ℝ) (423097774413/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4269/32768 : ℝ))) 1 (589505863353/1000000000000 : ℝ) (589505863357/1000000000000 : ℝ) (105774443601/250000000000 : ℝ) (423097774413/1000000000000 : ℝ) (253150909439/500000000000 : ℝ) (101260363777/200000000000 : ℝ) (99883656077/200000000000 : ℝ) (499418280393/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4269/32768 : ℝ))) 2 (253150909439/500000000000 : ℝ) (101260363777/200000000000 : ℝ) (99883656077/200000000000 : ℝ) (499418280393/1000000000000 : ℝ) (502860049631/1000000000000 : ℝ) (502860049639/1000000000000 : ℝ) (502848271091/1000000000000 : ℝ) (5028482711/10000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4269/32768 : ℝ))) 3 (502860049631/1000000000000 : ℝ) (502860049639/1000000000000 : ℝ) (502848271091/1000000000000 : ℝ) (5028482711/10000000000 : ℝ) (502854160361/1000000000000 : ℝ) (50285416037/100000000000 : ℝ) (251427080163/500000000000 : ℝ) (31428385021/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4269/32768 : ℝ))) 4 (502854160361/1000000000000 : ℝ) (50285416037/100000000000 : ℝ) (251427080163/500000000000 : ℝ) (31428385021/62500000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4269/32768 : ℝ))) 5 (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4269/32768 : ℝ))) 6 (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4269/32768 : ℝ))) 7 (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4269/32768 : ℝ)) hmem 8 (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4269/32768 : ℝ))) hcmem 8 (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4269/32768 : ℝ)) (495953514691/500000000000 : ℝ) (198381405877/200000000000 : ℝ) (502854160343/1000000000000 : ℝ) (502854160353/1000000000000 : ℝ) (796326111803/1000000000000 : ℝ) (398163055911/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1528_exp_lower
  have heNumeric : (2054910986677/1000000000000 : ℝ)/4 ≤ Real.exp (-10656989273527/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054910986677/1000000000000 : ℝ)/4 ≤ Real.exp ((8537/65536 : ℝ)-(398163055911/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8537/65536 : ℝ) (4269/32768 : ℝ) (398163055911/500000000000 : ℝ) (2054910986677/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1529; no trusted numerical premise.
theorem cover8_leaf1529_exp_radius : (49898310735137859/50000000000000000 : ℝ) ≤ Real.exp ((-8539/524288 : ℝ)/8) ∧ Real.exp ((-8539/524288 : ℝ)/8) ≤ (997966214702757181/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8539/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1529_exp_lower : (28753562528257217/31250000000000000 : ℝ) ≤ Real.exp ((-5328492965723/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328492965723/8000000000000 : ℝ)/8) ≤ (184022800180846189/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328492965723/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1529_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054911415907/1000000000000 : ℝ) ≤ 4*Real.exp (4269/32768 : ℝ)*Real.exp (-mu (radius 8 (8539/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054911415907/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8539/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1529_exp_radius
  have hrNumeric : (491922531821/500000000000 : ℝ) ≤ Real.exp (-8539/524288 : ℝ) ∧ Real.exp (-8539/524288 : ℝ) ≤ (983845063643/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491922531821/500000000000 : ℝ) ≤ (radius 8 (8539/65536 : ℝ)) ∧ (radius 8 (8539/65536 : ℝ)) ≤ (983845063643/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8539/65536 : ℝ)) (491922531821/500000000000 : ℝ) (983845063643/1000000000000 : ℝ) (179022039831/1000000000000 : ℝ) (179022039837/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8539/65536 : ℝ)) (491922531821/500000000000 : ℝ) (983845063643/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8539/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491922531821/500000000000 : ℝ) (983845063643/1000000000000 : ℝ) (991922531821/1000000000000 : ℝ) (495961265911/500000000000 : ℝ) (495944821437/500000000000 : ℝ) (247972410719/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8539/65536 : ℝ)) 1 (991922531821/1000000000000 : ℝ) (495961265911/500000000000 : ℝ) (495944821437/500000000000 : ℝ) (247972410719/250000000000 : ℝ) (991906087347/1000000000000 : ℝ) (991906087349/1000000000000 : ℝ) (991906087211/1000000000000 : ℝ) (991906087213/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8539/65536 : ℝ)) 2 (991906087347/1000000000000 : ℝ) (991906087349/1000000000000 : ℝ) (991906087211/1000000000000 : ℝ) (991906087213/1000000000000 : ℝ) (991906087279/1000000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8539/65536 : ℝ)) 3 (991906087279/1000000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8539/65536 : ℝ)) 4 (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8539/65536 : ℝ)) 5 (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8539/65536 : ℝ)) 6 (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8539/65536 : ℝ)) 7 (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8539/65536 : ℝ))) (179022039831/1000000000000 : ℝ) (179022039837/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8539/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179022039831/1000000000000 : ℝ) (179022039837/1000000000000 : ℝ) (117902203983/200000000000 : ℝ) (589511019919/1000000000000 : ℝ) (211554980933/500000000000 : ℝ) (211554980937/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8539/65536 : ℝ))) 1 (117902203983/200000000000 : ℝ) (589511019919/1000000000000 : ℝ) (211554980933/500000000000 : ℝ) (211554980937/500000000000 : ℝ) (50631049089/100000000000 : ℝ) (506310490897/1000000000000 : ℝ) (499427657579/1000000000000 : ℝ) (499427657587/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8539/65536 : ℝ))) 2 (50631049089/100000000000 : ℝ) (506310490897/1000000000000 : ℝ) (499427657579/1000000000000 : ℝ) (499427657587/1000000000000 : ℝ) (251434537117/500000000000 : ℝ) (251434537121/500000000000 : ℝ) (502857298319/1000000000000 : ℝ) (502857298327/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8539/65536 : ℝ))) 3 (251434537117/500000000000 : ℝ) (251434537121/500000000000 : ℝ) (502857298319/1000000000000 : ℝ) (502857298327/1000000000000 : ℝ) (125715796569/250000000000 : ℝ) (100572637257/200000000000 : ℝ) (251431593121/500000000000 : ℝ) (502863186251/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8539/65536 : ℝ))) 4 (125715796569/250000000000 : ℝ) (100572637257/200000000000 : ℝ) (251431593121/500000000000 : ℝ) (502863186251/1000000000000 : ℝ) (502863186259/1000000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8539/65536 : ℝ))) 5 (502863186259/1000000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8539/65536 : ℝ))) 6 (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8539/65536 : ℝ))) 7 (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8539/65536 : ℝ)) hmem 8 (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8539/65536 : ℝ))) hcmem 8 (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8539/65536 : ℝ)) (495953043639/500000000000 : ℝ) (991906087281/1000000000000 : ℝ) (251431593129/500000000000 : ℝ) (125715796567/250000000000 : ℝ) (796341161711/1000000000000 : ℝ) (796341161731/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1529_exp_lower
  have heNumeric : (2054911415907/1000000000000 : ℝ)/4 ≤ Real.exp (-5328492965723/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054911415907/1000000000000 : ℝ)/4 ≤ Real.exp ((4269/32768 : ℝ)-(796341161731/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4269/32768 : ℝ) (8539/65536 : ℝ) (796341161731/1000000000000 : ℝ) (2054911415907/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1530; no trusted numerical premise.
theorem cover8_leaf1530_exp_radius : (997965976769098643/1000000000000000000 : ℝ) ≤ Real.exp ((-2135/131072 : ℝ)/8) ∧ Real.exp ((-2135/131072 : ℝ)/8) ≤ (249491494192274661/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2135/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1530_exp_lower : (920114025064936929/1000000000000000000 : ℝ) ≤ Real.exp ((-10656982570373/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656982570373/16000000000000 : ℝ)/8) ≤ (92011402506493693/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656982570373/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1530_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256863980947/125000000000 : ℝ) ≤ 4*Real.exp (8539/65536 : ℝ)*Real.exp (-mu (radius 8 (2135/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (256863980947/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2135/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1530_exp_radius
  have hrNumeric : (245960796777/250000000000 : ℝ) ≤ Real.exp (-2135/131072 : ℝ) ∧ Real.exp (-2135/131072 : ℝ) ≤ (983843187109/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245960796777/250000000000 : ℝ) ≤ (radius 8 (2135/16384 : ℝ)) ∧ (radius 8 (2135/16384 : ℝ)) ≤ (983843187109/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2135/16384 : ℝ)) (245960796777/250000000000 : ℝ) (983843187109/1000000000000 : ℝ) (7161294093/40000000000 : ℝ) (44758088083/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2135/16384 : ℝ)) (245960796777/250000000000 : ℝ) (983843187109/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2135/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245960796777/250000000000 : ℝ) (983843187109/1000000000000 : ℝ) (495960796777/500000000000 : ℝ) (198384318711/200000000000 : ℝ) (198377739387/200000000000 : ℝ) (123986087117/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2135/16384 : ℝ)) 1 (495960796777/500000000000 : ℝ) (198384318711/200000000000 : ℝ) (198377739387/200000000000 : ℝ) (123986087117/125000000000 : ℝ) (247976286311/250000000000 : ℝ) (495952572623/500000000000 : ℝ) (247976286277/250000000000 : ℝ) (99190514511/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2135/16384 : ℝ)) 2 (247976286311/250000000000 : ℝ) (495952572623/500000000000 : ℝ) (247976286277/250000000000 : ℝ) (99190514511/100000000000 : ℝ) (123988143147/125000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2135/16384 : ℝ)) 3 (123988143147/125000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2135/16384 : ℝ)) 4 (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2135/16384 : ℝ)) 5 (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2135/16384 : ℝ)) 6 (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2135/16384 : ℝ)) 7 (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2135/16384 : ℝ))) (7161294093/40000000000 : ℝ) (44758088083/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2135/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7161294093/40000000000 : ℝ) (44758088083/250000000000 : ℝ) (294758088081/500000000000 : ℝ) (294758088083/500000000000 : ℝ) (52890268529/125000000000 : ℝ) (423122148241/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2135/16384 : ℝ))) 1 (294758088081/500000000000 : ℝ) (294758088083/500000000000 : ℝ) (52890268529/125000000000 : ℝ) (423122148241/1000000000000 : ℝ) (506319162197/1000000000000 : ℝ) (126579790551/250000000000 : ℝ) (62429629243/125000000000 : ℝ) (15607407311/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2135/16384 : ℝ))) 2 (506319162197/1000000000000 : ℝ) (126579790551/250000000000 : ℝ) (62429629243/125000000000 : ℝ) (15607407311/31250000000 : ℝ) (50287809807/100000000000 : ℝ) (251439049039/500000000000 : ℝ) (251433162389/500000000000 : ℝ) (502866324787/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2135/16384 : ℝ))) 3 (50287809807/100000000000 : ℝ) (251439049039/500000000000 : ℝ) (251433162389/500000000000 : ℝ) (502866324787/1000000000000 : ℝ) (15714756607/31250000000 : ℝ) (502872211433/1000000000000 : ℝ) (502872211389/1000000000000 : ℝ) (502872211399/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2135/16384 : ℝ))) 4 (15714756607/31250000000 : ℝ) (502872211433/1000000000000 : ℝ) (502872211389/1000000000000 : ℝ) (502872211399/1000000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2135/16384 : ℝ))) 5 (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2135/16384 : ℝ))) 6 (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2135/16384 : ℝ))) 7 (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2135/16384 : ℝ)) hmem 8 (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2135/16384 : ℝ))) hcmem 8 (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2135/16384 : ℝ)) (39676205807/40000000000 : ℝ) (495952572589/500000000000 : ℝ) (251436105703/500000000000 : ℝ) (62859026427/125000000000 : ℝ) (796356210433/1000000000000 : ℝ) (796356210453/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1530_exp_lower
  have heNumeric : (256863980947/125000000000 : ℝ)/4 ≤ Real.exp (-10656982570373/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256863980947/125000000000 : ℝ)/4 ≤ Real.exp ((8539/65536 : ℝ)-(796356210453/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8539/65536 : ℝ) (2135/16384 : ℝ) (796356210453/1000000000000 : ℝ) (256863980947/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1531; no trusted numerical premise.
theorem cover8_leaf1531_exp_radius : (498982869417748417/500000000000000000 : ℝ) ≤ Real.exp ((-8541/524288 : ℝ)/8) ∧ Real.exp ((-8541/524288 : ℝ)/8) ≤ (199593147767099367/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8541/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1531_exp_lower : (23002851234088641/25000000000000000 : ℝ) ≤ Real.exp ((-2664244797529/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664244797529/4000000000000 : ℝ)/8) ≤ (920114049363545641/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664244797529/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1531_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912281709/1000000000000 : ℝ) ≤ 4*Real.exp (2135/16384 : ℝ)*Real.exp (-mu (radius 8 (8541/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912281709/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8541/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1531_exp_radius
  have hrNumeric : (491920655289/500000000000 : ℝ) ≤ Real.exp (-8541/524288 : ℝ) ∧ Real.exp (-8541/524288 : ℝ) ≤ (983841310579/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491920655289/500000000000 : ℝ) ≤ (radius 8 (8541/65536 : ℝ)) ∧ (radius 8 (8541/65536 : ℝ)) ≤ (983841310579/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8541/65536 : ℝ)) (491920655289/500000000000 : ℝ) (983841310579/1000000000000 : ℝ) (22380333023/125000000000 : ℝ) (17904266419/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8541/65536 : ℝ)) (491920655289/500000000000 : ℝ) (983841310579/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8541/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491920655289/500000000000 : ℝ) (983841310579/1000000000000 : ℝ) (991920655289/1000000000000 : ℝ) (99192065529/100000000000 : ℝ) (991887750997/1000000000000 : ℝ) (495943875499/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8541/65536 : ℝ)) 1 (991920655289/1000000000000 : ℝ) (99192065529/100000000000 : ℝ) (991887750997/1000000000000 : ℝ) (495943875499/500000000000 : ℝ) (991904203143/1000000000000 : ℝ) (123988025393/125000000000 : ℝ) (495952101503/500000000000 : ℝ) (3874625793/3906250000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8541/65536 : ℝ)) 2 (991904203143/1000000000000 : ℝ) (123988025393/125000000000 : ℝ) (495952101503/500000000000 : ℝ) (3874625793/3906250000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8541/65536 : ℝ)) 3 (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8541/65536 : ℝ)) 4 (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8541/65536 : ℝ)) 5 (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8541/65536 : ℝ)) 6 (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8541/65536 : ℝ)) 7 (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8541/65536 : ℝ))) (22380333023/125000000000 : ℝ) (17904266419/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8541/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22380333023/125000000000 : ℝ) (17904266419/100000000000 : ℝ) (147380333023/250000000000 : ℝ) (117904266419/200000000000 : ℝ) (423134333497/1000000000000 : ℝ) (84626866701/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8541/65536 : ℝ))) 1 (147380333023/250000000000 : ℝ) (117904266419/200000000000 : ℝ) (423134333497/1000000000000 : ℝ) (84626866701/200000000000 : ℝ) (253163916397/500000000000 : ℝ) (632909791/1250000000 : ℝ) (249723204737/500000000000 : ℝ) (499446409481/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8541/65536 : ℝ))) 2 (253163916397/500000000000 : ℝ) (632909791/1250000000 : ℝ) (249723204737/500000000000 : ℝ) (499446409481/1000000000000 : ℝ) (251443560567/500000000000 : ℝ) (502887121141/1000000000000 : ℝ) (100575070093/200000000000 : ℝ) (62859418809/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8541/65536 : ℝ))) 3 (251443560567/500000000000 : ℝ) (502887121141/1000000000000 : ℝ) (100575070093/200000000000 : ℝ) (62859418809/125000000000 : ℝ) (502881235799/1000000000000 : ℝ) (502881235807/1000000000000 : ℝ) (100576247153/200000000000 : ℝ) (502881235773/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8541/65536 : ℝ))) 4 (502881235799/1000000000000 : ℝ) (502881235807/1000000000000 : ℝ) (100576247153/200000000000 : ℝ) (502881235773/1000000000000 : ℝ) (251440617891/500000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8541/65536 : ℝ))) 5 (251440617891/500000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8541/65536 : ℝ))) 6 (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8541/65536 : ℝ))) 7 (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8541/65536 : ℝ)) hmem 8 (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8541/65536 : ℝ))) hcmem 8 (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8541/65536 : ℝ)) (495952101537/500000000000 : ℝ) (247976050769/250000000000 : ℝ) (502881235781/1000000000000 : ℝ) (50288123579/100000000000 : ℝ) (796371257959/1000000000000 : ℝ) (99546407247/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1531_exp_lower
  have heNumeric : (2054912281709/1000000000000 : ℝ)/4 ≤ Real.exp (-2664244797529/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912281709/1000000000000 : ℝ)/4 ≤ Real.exp ((2135/16384 : ℝ)-(99546407247/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2135/16384 : ℝ) (8541/65536 : ℝ) (99546407247/125000000000 : ℝ) (2054912281709/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1532; no trusted numerical premise.
theorem cover8_leaf1532_exp_radius : (997965500901951753/1000000000000000000 : ℝ) ≤ Real.exp ((-4271/262144 : ℝ)/8) ∧ Real.exp ((-4271/262144 : ℝ)/8) ≤ (498982750450975877/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4271/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1532_exp_lower : (184022814759712381/200000000000000000 : ℝ) ≤ Real.exp ((-10656975790883/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656975790883/16000000000000 : ℝ)/8) ≤ (460057036899280953/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656975790883/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1532_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912718279/1000000000000 : ℝ) ≤ 4*Real.exp (8541/65536 : ℝ)*Real.exp (-mu (radius 8 (4271/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912718279/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4271/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1532_exp_radius
  have hrNumeric : (983839434051/1000000000000 : ℝ) ≤ Real.exp (-4271/262144 : ℝ) ∧ Real.exp (-4271/262144 : ℝ) ≤ (245959858513/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983839434051/1000000000000 : ℝ) ≤ (radius 8 (4271/32768 : ℝ)) ∧ (radius 8 (4271/32768 : ℝ)) ≤ (245959858513/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4271/32768 : ℝ)) (983839434051/1000000000000 : ℝ) (245959858513/250000000000 : ℝ) (44763243853/250000000000 : ℝ) (179052975419/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4271/32768 : ℝ)) (983839434051/1000000000000 : ℝ) (245959858513/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4271/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983839434051/1000000000000 : ℝ) (245959858513/250000000000 : ℝ) (39676788681/40000000000 : ℝ) (495959858513/500000000000 : ℝ) (991886805059/1000000000000 : ℝ) (49594340253/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4271/32768 : ℝ)) 1 (39676788681/40000000000 : ℝ) (495959858513/500000000000 : ℝ) (991886805059/1000000000000 : ℝ) (49594340253/50000000000 : ℝ) (495951630521/500000000000 : ℝ) (991903261043/1000000000000 : ℝ) (198380652181/200000000000 : ℝ) (991903260907/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4271/32768 : ℝ)) 2 (495951630521/500000000000 : ℝ) (991903261043/1000000000000 : ℝ) (198380652181/200000000000 : ℝ) (991903260907/1000000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4271/32768 : ℝ)) 3 (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4271/32768 : ℝ)) 4 (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4271/32768 : ℝ)) 5 (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4271/32768 : ℝ)) 6 (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4271/32768 : ℝ)) 7 (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4271/32768 : ℝ))) (44763243853/250000000000 : ℝ) (179052975419/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4271/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44763243853/250000000000 : ℝ) (179052975419/1000000000000 : ℝ) (294763243853/500000000000 : ℝ) (58952648771/100000000000 : ℝ) (13223328677/31250000000 : ℝ) (211573258837/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4271/32768 : ℝ))) 1 (294763243853/500000000000 : ℝ) (58952648771/100000000000 : ℝ) (13223328677/31250000000 : ℝ) (211573258837/500000000000 : ℝ) (101267300537/200000000000 : ℝ) (126584125673/250000000000 : ℝ) (124863946043/250000000000 : ℝ) (499455784181/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4271/32768 : ℝ))) 2 (101267300537/200000000000 : ℝ) (126584125673/250000000000 : ℝ) (124863946043/250000000000 : ℝ) (499455784181/1000000000000 : ℝ) (125724035857/250000000000 : ℝ) (502896143437/1000000000000 : ℝ) (251442187691/500000000000 : ℝ) (502884375391/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4271/32768 : ℝ))) 3 (125724035857/250000000000 : ℝ) (502896143437/1000000000000 : ℝ) (251442187691/500000000000 : ℝ) (502884375391/1000000000000 : ℝ) (100578051881/200000000000 : ℝ) (251445129707/500000000000 : ℝ) (50289025937/100000000000 : ℝ) (25144512969/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4271/32768 : ℝ))) 4 (100578051881/200000000000 : ℝ) (251445129707/500000000000 : ℝ) (50289025937/100000000000 : ℝ) (25144512969/50000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4271/32768 : ℝ))) 5 (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4271/32768 : ℝ))) 6 (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4271/32768 : ℝ))) 7 (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4271/32768 : ℝ)) hmem 8 (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4271/32768 : ℝ))) hcmem 8 (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4271/32768 : ℝ)) (991903260973/1000000000000 : ℝ) (39676130439/40000000000 : ℝ) (502890259387/1000000000000 : ℝ) (502890259397/1000000000000 : ℝ) (398193152147/500000000000 : ℝ) (796386304313/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1532_exp_lower
  have heNumeric : (2054912718279/1000000000000 : ℝ)/4 ≤ Real.exp (-10656975790883/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912718279/1000000000000 : ℝ)/4 ≤ Real.exp ((8541/65536 : ℝ)-(796386304313/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8541/65536 : ℝ) (4271/32768 : ℝ) (796386304313/1000000000000 : ℝ) (2054912718279/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1533; no trusted numerical premise.
theorem cover8_leaf1533_exp_radius : (997965262968463399/1000000000000000000 : ℝ) ≤ Real.exp ((-8543/524288 : ℝ)/8) ∧ Real.exp ((-8543/524288 : ℝ)/8) ≤ (4989826314842317/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8543/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1533_exp_lower : (920114098371250891/1000000000000000000 : ℝ) ≤ Real.exp ((-5328486186249/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328486186249/8000000000000 : ℝ)/8) ≤ (230028524592812723/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328486186249/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1533_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205491315731/100000000000 : ℝ) ≤ 4*Real.exp (4271/32768 : ℝ)*Real.exp (-mu (radius 8 (8543/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205491315731/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8543/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1533_exp_radius
  have hrNumeric : (122979694691/125000000000 : ℝ) ≤ Real.exp (-8543/524288 : ℝ) ∧ Real.exp (-8543/524288 : ℝ) ≤ (983837557529/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122979694691/125000000000 : ℝ) ≤ (radius 8 (8543/65536 : ℝ)) ∧ (radius 8 (8543/65536 : ℝ)) ≤ (983837557529/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8543/65536 : ℝ)) (122979694691/125000000000 : ℝ) (983837557529/1000000000000 : ℝ) (89531643003/500000000000 : ℝ) (44765821503/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8543/65536 : ℝ)) (122979694691/125000000000 : ℝ) (983837557529/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8543/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122979694691/125000000000 : ℝ) (983837557529/1000000000000 : ℝ) (247979694691/250000000000 : ℝ) (198383755753/200000000000 : ℝ) (495942929561/500000000000 : ℝ) (247971464781/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8543/65536 : ℝ)) 1 (247979694691/250000000000 : ℝ) (198383755753/200000000000 : ℝ) (495942929561/500000000000 : ℝ) (247971464781/250000000000 : ℝ) (991902318943/1000000000000 : ℝ) (198380463789/200000000000 : ℝ) (495951159403/500000000000 : ℝ) (123987789851/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8543/65536 : ℝ)) 2 (991902318943/1000000000000 : ℝ) (198380463789/200000000000 : ℝ) (495951159403/500000000000 : ℝ) (123987789851/125000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8543/65536 : ℝ)) 3 (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8543/65536 : ℝ)) 4 (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8543/65536 : ℝ)) 5 (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8543/65536 : ℝ)) 6 (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8543/65536 : ℝ)) 7 (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8543/65536 : ℝ))) (89531643003/500000000000 : ℝ) (44765821503/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8543/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89531643003/500000000000 : ℝ) (44765821503/250000000000 : ℝ) (589531643003/1000000000000 : ℝ) (294765821503/500000000000 : ℝ) (105789675183/250000000000 : ℝ) (423158700741/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8543/65536 : ℝ))) 1 (589531643003/1000000000000 : ℝ) (294765821503/500000000000 : ℝ) (105789675183/250000000000 : ℝ) (423158700741/1000000000000 : ℝ) (506345171867/1000000000000 : ℝ) (253172585937/500000000000 : ℝ) (499465158037/1000000000000 : ℝ) (99893031609/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8543/65536 : ℝ))) 2 (506345171867/1000000000000 : ℝ) (253172585937/500000000000 : ℝ) (499465158037/1000000000000 : ℝ) (99893031609/200000000000 : ℝ) (62863145619/125000000000 : ℝ) (3143157281/6250000000 : ℝ) (502893399527/1000000000000 : ℝ) (100578679907/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8543/65536 : ℝ))) 3 (62863145619/125000000000 : ℝ) (3143157281/6250000000 : ℝ) (502893399527/1000000000000 : ℝ) (100578679907/200000000000 : ℝ) (502899282239/1000000000000 : ℝ) (62862410281/125000000000 : ℝ) (100579856441/200000000000 : ℝ) (251449641107/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8543/65536 : ℝ))) 4 (502899282239/1000000000000 : ℝ) (62862410281/125000000000 : ℝ) (100579856441/200000000000 : ℝ) (251449641107/500000000000 : ℝ) (251449641111/500000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8543/65536 : ℝ))) 5 (251449641111/500000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8543/65536 : ℝ))) 6 (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8543/65536 : ℝ))) 7 (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8543/65536 : ℝ)) hmem 8 (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8543/65536 : ℝ))) hcmem 8 (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8543/65536 : ℝ)) (495951159437/500000000000 : ℝ) (991902318877/1000000000000 : ℝ) (502899282221/1000000000000 : ℝ) (502899282231/1000000000000 : ℝ) (398200674717/500000000000 : ℝ) (796401349453/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1533_exp_lower
  have heNumeric : (205491315731/100000000000 : ℝ)/4 ≤ Real.exp (-5328486186249/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205491315731/100000000000 : ℝ)/4 ≤ Real.exp ((4271/32768 : ℝ)-(796401349453/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4271/32768 : ℝ) (8543/65536 : ℝ) (796401349453/1000000000000 : ℝ) (205491315731/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1534; no trusted numerical premise.
theorem cover8_leaf1534_exp_radius : (498982512517515887/500000000000000000 : ℝ) ≤ Real.exp ((-267/16384 : ℝ)/8) ∧ Real.exp ((-267/16384 : ℝ)/8) ≤ (39918601001401271/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-267/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1534_exp_lower : (460057061540863811/500000000000000000 : ℝ) ≤ Real.exp ((-2131393786989/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131393786989/3200000000000 : ℝ)/8) ≤ (920114123081727623/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131393786989/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1534_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027456799401/500000000000 : ℝ) ≤ 4*Real.exp (8543/65536 : ℝ)*Real.exp (-mu (radius 8 (267/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (1027456799401/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (267/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1534_exp_radius
  have hrNumeric : (983835681009/1000000000000 : ℝ) ≤ Real.exp (-267/16384 : ℝ) ∧ Real.exp (-267/16384 : ℝ) ≤ (98383568101/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983835681009/1000000000000 : ℝ) ≤ (radius 8 (267/2048 : ℝ)) ∧ (radius 8 (267/2048 : ℝ)) ≤ (98383568101/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (267/2048 : ℝ)) (983835681009/1000000000000 : ℝ) (98383568101/100000000000 : ℝ) (44768398991/250000000000 : ℝ) (17907359597/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (267/2048 : ℝ)) (983835681009/1000000000000 : ℝ) (98383568101/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (267/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983835681009/1000000000000 : ℝ) (98383568101/100000000000 : ℝ) (123989730063/125000000000 : ℝ) (198383568101/200000000000 : ℝ) (991884913187/1000000000000 : ℝ) (991884913189/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (267/2048 : ℝ)) 1 (123989730063/125000000000 : ℝ) (198383568101/200000000000 : ℝ) (991884913187/1000000000000 : ℝ) (991884913189/1000000000000 : ℝ) (198380275369/200000000000 : ℝ) (991901376847/1000000000000 : ℝ) (247975344177/250000000000 : ℝ) (991901376711/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (267/2048 : ℝ)) 2 (198380275369/200000000000 : ℝ) (991901376847/1000000000000 : ℝ) (247975344177/250000000000 : ℝ) (991901376711/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (267/2048 : ℝ)) 3 (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (267/2048 : ℝ)) 4 (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (267/2048 : ℝ)) 5 (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (267/2048 : ℝ)) 6 (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (267/2048 : ℝ)) 7 (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (267/2048 : ℝ))) (44768398991/250000000000 : ℝ) (17907359597/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (267/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44768398991/250000000000 : ℝ) (17907359597/100000000000 : ℝ) (294768398991/500000000000 : ℝ) (117907359597/200000000000 : ℝ) (211585441349/500000000000 : ℝ) (211585441353/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (267/2048 : ℝ))) 1 (294768398991/500000000000 : ℝ) (117907359597/200000000000 : ℝ) (211585441349/500000000000 : ℝ) (211585441353/500000000000 : ℝ) (25317692017/50000000000 : ℝ) (253176920173/500000000000 : ℝ) (499474531067/1000000000000 : ℝ) (249737265537/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (267/2048 : ℝ))) 2 (25317692017/50000000000 : ℝ) (253176920173/500000000000 : ℝ) (499474531067/1000000000000 : ℝ) (249737265537/500000000000 : ℝ) (502914185703/1000000000000 : ℝ) (50291418571/100000000000 : ℝ) (502902422899/1000000000000 : ℝ) (251451211453/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (267/2048 : ℝ))) 3 (502914185703/1000000000000 : ℝ) (50291418571/100000000000 : ℝ) (502902422899/1000000000000 : ℝ) (251451211453/500000000000 : ℝ) (502908304301/1000000000000 : ℝ) (125727076077/250000000000 : ℝ) (251454152133/500000000000 : ℝ) (251454152137/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (267/2048 : ℝ))) 4 (502908304301/1000000000000 : ℝ) (125727076077/250000000000 : ℝ) (251454152133/500000000000 : ℝ) (251454152137/500000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (267/2048 : ℝ))) 5 (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (267/2048 : ℝ))) 6 (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (267/2048 : ℝ))) 7 (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (267/2048 : ℝ)) hmem 8 (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (267/2048 : ℝ))) hcmem 8 (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (267/2048 : ℝ)) (123987672097/125000000000 : ℝ) (991901376779/1000000000000 : ℝ) (502908304283/1000000000000 : ℝ) (502908304291/1000000000000 : ℝ) (796416393379/1000000000000 : ℝ) (159283278679/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1534_exp_lower
  have heNumeric : (1027456799401/500000000000 : ℝ)/4 ≤ Real.exp (-2131393786989/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027456799401/500000000000 : ℝ)/4 ≤ Real.exp ((8543/65536 : ℝ)-(159283278679/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8543/65536 : ℝ) (267/2048 : ℝ) (159283278679/200000000000 : ℝ) (1027456799401/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1535; no trusted numerical premise.
theorem cover8_leaf1535_exp_radius : (249491196775414219/250000000000000000 : ℝ) ≤ Real.exp ((-8545/524288 : ℝ)/8) ∧ Real.exp ((-8545/524288 : ℝ)/8) ≤ (997964787101656877/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8545/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1535_exp_lower : (115014268491047739/125000000000000000 : ℝ) ≤ Real.exp ((-666060342403/1000000000000 : ℝ)/8) ∧ Real.exp ((-666060342403/1000000000000 : ℝ)/8) ≤ (920114147928381913/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666060342403/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1535_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054914042727/1000000000000 : ℝ) ≤ 4*Real.exp (267/2048 : ℝ)*Real.exp (-mu (radius 8 (8545/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054914042727/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8545/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1535_exp_radius
  have hrNumeric : (983833804493/1000000000000 : ℝ) ≤ Real.exp (-8545/524288 : ℝ) ∧ Real.exp (-8545/524288 : ℝ) ≤ (491916902247/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983833804493/1000000000000 : ℝ) ≤ (radius 8 (8545/65536 : ℝ)) ∧ (radius 8 (8545/65536 : ℝ)) ≤ (491916902247/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8545/65536 : ℝ)) (983833804493/1000000000000 : ℝ) (491916902247/500000000000 : ℝ) (44770976323/250000000000 : ℝ) (179083905299/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8545/65536 : ℝ)) (983833804493/1000000000000 : ℝ) (491916902247/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8545/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983833804493/1000000000000 : ℝ) (491916902247/500000000000 : ℝ) (495958451123/500000000000 : ℝ) (991916902247/1000000000000 : ℝ) (247970991813/250000000000 : ℝ) (495941983627/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8545/65536 : ℝ)) 1 (495958451123/500000000000 : ℝ) (991916902247/1000000000000 : ℝ) (247970991813/250000000000 : ℝ) (495941983627/500000000000 : ℝ) (991900434749/1000000000000 : ℝ) (991900434751/1000000000000 : ℝ) (247975108653/250000000000 : ℝ) (495950217307/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8545/65536 : ℝ)) 2 (991900434749/1000000000000 : ℝ) (991900434751/1000000000000 : ℝ) (247975108653/250000000000 : ℝ) (495950217307/500000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8545/65536 : ℝ)) 3 (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8545/65536 : ℝ)) 4 (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8545/65536 : ℝ)) 5 (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8545/65536 : ℝ)) 6 (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8545/65536 : ℝ)) 7 (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8545/65536 : ℝ))) (44770976323/250000000000 : ℝ) (179083905299/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8545/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44770976323/250000000000 : ℝ) (179083905299/1000000000000 : ℝ) (294770976323/500000000000 : ℝ) (11790839053/20000000000 : ℝ) (423183063569/1000000000000 : ℝ) (211591531789/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8545/65536 : ℝ))) 1 (294770976323/500000000000 : ℝ) (11790839053/20000000000 : ℝ) (423183063569/1000000000000 : ℝ) (211591531789/500000000000 : ℝ) (506362508107/1000000000000 : ℝ) (253181254057/500000000000 : ℝ) (499483903267/1000000000000 : ℝ) (19979356131/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8545/65536 : ℝ))) 2 (506362508107/1000000000000 : ℝ) (253181254057/500000000000 : ℝ) (499483903267/1000000000000 : ℝ) (19979356131/40000000000 : ℝ) (502923205687/1000000000000 : ℝ) (100584641139/200000000000 : ℝ) (251455722751/500000000000 : ℝ) (50291144551/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8545/65536 : ℝ))) 3 (502923205687/1000000000000 : ℝ) (100584641139/200000000000 : ℝ) (251455722751/500000000000 : ℝ) (50291144551/100000000000 : ℝ) (251458662797/500000000000 : ℝ) (502917325603/1000000000000 : ℝ) (12572933139/25000000000 : ℝ) (502917325569/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8545/65536 : ℝ))) 4 (251458662797/500000000000 : ℝ) (502917325603/1000000000000 : ℝ) (12572933139/25000000000 : ℝ) (502917325569/1000000000000 : ℝ) (502917325577/1000000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8545/65536 : ℝ))) 5 (502917325577/1000000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8545/65536 : ℝ))) 6 (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8545/65536 : ℝ))) 7 (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8545/65536 : ℝ)) hmem 8 (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8545/65536 : ℝ))) hcmem 8 (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8545/65536 : ℝ)) (24797510867/25000000000 : ℝ) (991900434683/1000000000000 : ℝ) (62864665697/125000000000 : ℝ) (251458662793/500000000000 : ℝ) (796431436133/1000000000000 : ℝ) (796431436153/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1535_exp_lower
  have heNumeric : (2054914042727/1000000000000 : ℝ)/4 ≤ Real.exp (-666060342403/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054914042727/1000000000000 : ℝ)/4 ≤ Real.exp ((267/2048 : ℝ)-(796431436153/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (267/2048 : ℝ) (8545/65536 : ℝ) (796431436153/1000000000000 : ℝ) (2054914042727/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1536; no trusted numerical premise.
theorem cover8_leaf1536_exp_radius : (199592909833667741/200000000000000000 : ℝ) ≤ Real.exp ((-4273/262144 : ℝ)/8) ∧ Real.exp ((-4273/262144 : ℝ)/8) ≤ (498982274584169353/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4273/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1536_exp_lower : (115014271614117373/125000000000000000 : ℝ) ≤ Real.exp ((-10656962002767/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656962002767/16000000000000 : ℝ)/8) ≤ (184022834582587797/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656962002767/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1536_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513728622279/250000000000 : ℝ) ≤ 4*Real.exp (8545/65536 : ℝ)*Real.exp (-mu (radius 8 (4273/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513728622279/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4273/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1536_exp_radius
  have hrNumeric : (983831927981/1000000000000 : ℝ) ≤ Real.exp (-4273/262144 : ℝ) ∧ Real.exp (-4273/262144 : ℝ) ≤ (491915963991/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983831927981/1000000000000 : ℝ) ≤ (radius 8 (4273/32768 : ℝ)) ∧ (radius 8 (4273/32768 : ℝ)) ≤ (491915963991/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4273/32768 : ℝ)) (983831927981/1000000000000 : ℝ) (491915963991/500000000000 : ℝ) (35818842797/200000000000 : ℝ) (22386776749/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4273/32768 : ℝ)) (983831927981/1000000000000 : ℝ) (491915963991/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4273/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983831927981/1000000000000 : ℝ) (491915963991/500000000000 : ℝ) (99191596399/100000000000 : ℝ) (991915963991/1000000000000 : ℝ) (991883021319/1000000000000 : ℝ) (24797075533/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4273/32768 : ℝ)) 1 (99191596399/100000000000 : ℝ) (991915963991/1000000000000 : ℝ) (991883021319/1000000000000 : ℝ) (24797075533/25000000000 : ℝ) (495949746327/500000000000 : ℝ) (61993718291/62500000000 : ℝ) (991899492517/1000000000000 : ℝ) (991899492519/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4273/32768 : ℝ)) 2 (495949746327/500000000000 : ℝ) (61993718291/62500000000 : ℝ) (991899492517/1000000000000 : ℝ) (991899492519/1000000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4273/32768 : ℝ)) 3 (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4273/32768 : ℝ)) 4 (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4273/32768 : ℝ)) 5 (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4273/32768 : ℝ)) 6 (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4273/32768 : ℝ)) 7 (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4273/32768 : ℝ))) (35818842797/200000000000 : ℝ) (22386776749/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4273/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35818842797/200000000000 : ℝ) (22386776749/125000000000 : ℝ) (36846694187/62500000000 : ℝ) (147386776749/250000000000 : ℝ) (423195243339/1000000000000 : ℝ) (105798810837/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4273/32768 : ℝ))) 1 (36846694187/62500000000 : ℝ) (147386776749/250000000000 : ℝ) (423195243339/1000000000000 : ℝ) (105798810837/250000000000 : ℝ) (101274235033/200000000000 : ℝ) (126592793793/250000000000 : ℝ) (62436659329/125000000000 : ℝ) (6243665933/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4273/32768 : ℝ))) 2 (101274235033/200000000000 : ℝ) (126592793793/250000000000 : ℝ) (62436659329/125000000000 : ℝ) (6243665933/12500000000 : ℝ) (251466112449/500000000000 : ℝ) (251466112453/500000000000 : ℝ) (125730116833/250000000000 : ℝ) (502920467341/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4273/32768 : ℝ))) 3 (251466112449/500000000000 : ℝ) (251466112453/500000000000 : ℝ) (125730116833/250000000000 : ℝ) (502920467341/1000000000000 : ℝ) (100585269223/200000000000 : ℝ) (125731586531/250000000000 : ℝ) (3143289663/6250000000 : ℝ) (50292634609/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4273/32768 : ℝ))) 4 (100585269223/200000000000 : ℝ) (125731586531/250000000000 : ℝ) (3143289663/6250000000 : ℝ) (50292634609/100000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4273/32768 : ℝ))) 5 (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4273/32768 : ℝ))) 6 (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4273/32768 : ℝ))) 7 (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4273/32768 : ℝ)) hmem 8 (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4273/32768 : ℝ))) hcmem 8 (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4273/32768 : ℝ)) (198379898517/200000000000 : ℝ) (247974873147/250000000000 : ℝ) (502926346097/1000000000000 : ℝ) (502926346107/1000000000000 : ℝ) (796446477693/1000000000000 : ℝ) (49777904857/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1536_exp_lower
  have heNumeric : (513728622279/250000000000 : ℝ)/4 ≤ Real.exp (-10656962002767/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513728622279/250000000000 : ℝ)/4 ≤ Real.exp ((8545/65536 : ℝ)-(49777904857/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8545/65536 : ℝ) (4273/32768 : ℝ) (49777904857/62500000000 : ℝ) (513728622279/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1537; no trusted numerical premise.
theorem cover8_leaf1537_exp_radius : (997964311235077263/1000000000000000000 : ℝ) ≤ Real.exp ((-8547/524288 : ℝ)/8) ∧ Real.exp ((-8547/524288 : ℝ)/8) ≤ (62372769452192329/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8547/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1537_exp_lower : (18402283960675773/20000000000000000 : ℝ) ≤ Real.exp ((-5328479254063/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328479254063/8000000000000 : ℝ)/8) ≤ (920114198033788651/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328479254063/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1537_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745746897/50000000000 : ℝ) ≤ 4*Real.exp (4273/32768 : ℝ)*Real.exp (-mu (radius 8 (8547/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (102745746897/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8547/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1537_exp_radius
  have hrNumeric : (61489378217/62500000000 : ℝ) ≤ Real.exp (-8547/524288 : ℝ) ∧ Real.exp (-8547/524288 : ℝ) ≤ (983830051473/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61489378217/62500000000 : ℝ) ≤ (radius 8 (8547/65536 : ℝ)) ∧ (radius 8 (8547/65536 : ℝ)) ≤ (983830051473/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8547/65536 : ℝ)) (61489378217/62500000000 : ℝ) (983830051473/1000000000000 : ℝ) (179104522049/1000000000000 : ℝ) (22388065257/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8547/65536 : ℝ)) (61489378217/62500000000 : ℝ) (983830051473/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8547/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61489378217/62500000000 : ℝ) (983830051473/1000000000000 : ℝ) (123989378217/125000000000 : ℝ) (991915025737/1000000000000 : ℝ) (198376415077/200000000000 : ℝ) (991882075387/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8547/65536 : ℝ)) 1 (123989378217/125000000000 : ℝ) (991915025737/1000000000000 : ℝ) (198376415077/200000000000 : ℝ) (991882075387/1000000000000 : ℝ) (6199365941/6250000000 : ℝ) (495949275281/500000000000 : ℝ) (991898550423/1000000000000 : ℝ) (495949275213/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8547/65536 : ℝ)) 2 (6199365941/6250000000 : ℝ) (495949275281/500000000000 : ℝ) (991898550423/1000000000000 : ℝ) (495949275213/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8547/65536 : ℝ)) 3 (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8547/65536 : ℝ)) 4 (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8547/65536 : ℝ)) 5 (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8547/65536 : ℝ)) 6 (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8547/65536 : ℝ)) 7 (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8547/65536 : ℝ))) (179104522049/1000000000000 : ℝ) (22388065257/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8547/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179104522049/1000000000000 : ℝ) (22388065257/125000000000 : ℝ) (18423508157/31250000000 : ℝ) (147388065257/250000000000 : ℝ) (84641484403/200000000000 : ℝ) (52900927753/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8547/65536 : ℝ))) 1 (18423508157/31250000000 : ℝ) (147388065257/250000000000 : ℝ) (84641484403/200000000000 : ℝ) (52900927753/125000000000 : ℝ) (506379841519/1000000000000 : ℝ) (253189920763/500000000000 : ℝ) (499502645169/1000000000000 : ℝ) (499502645177/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8547/65536 : ℝ))) 2 (506379841519/1000000000000 : ℝ) (253189920763/500000000000 : ℝ) (499502645169/1000000000000 : ℝ) (499502645177/1000000000000 : ℝ) (31433827709/62500000000 : ℝ) (62867655419/125000000000 : ℝ) (125732372099/250000000000 : ℝ) (100585897681/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8547/65536 : ℝ))) 3 (31433827709/62500000000 : ℝ) (62867655419/125000000000 : ℝ) (125732372099/250000000000 : ℝ) (100585897681/200000000000 : ℝ) (50293536587/100000000000 : ℝ) (502935365879/1000000000000 : ℝ) (100587073167/200000000000 : ℝ) (100587073169/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8547/65536 : ℝ))) 4 (50293536587/100000000000 : ℝ) (502935365879/1000000000000 : ℝ) (100587073167/200000000000 : ℝ) (100587073169/200000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8547/65536 : ℝ))) 5 (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8547/65536 : ℝ))) 6 (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8547/65536 : ℝ))) 7 (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8547/65536 : ℝ)) hmem 8 (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8547/65536 : ℝ))) hcmem 8 (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8547/65536 : ℝ)) (991898550491/1000000000000 : ℝ) (495949275247/500000000000 : ℝ) (125733841463/250000000000 : ℝ) (251467682931/500000000000 : ℝ) (796461518067/1000000000000 : ℝ) (398230759043/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1537_exp_lower
  have heNumeric : (102745746897/50000000000 : ℝ)/4 ≤ Real.exp (-5328479254063/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745746897/50000000000 : ℝ)/4 ≤ Real.exp ((4273/32768 : ℝ)-(398230759043/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4273/32768 : ℝ) (8547/65536 : ℝ) (398230759043/500000000000 : ℝ) (102745746897/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1538; no trusted numerical premise.
theorem cover8_leaf1538_exp_radius : (249491018325468137/250000000000000000 : ℝ) ≤ Real.exp ((-2137/131072 : ℝ)/8) ∧ Real.exp ((-2137/131072 : ℝ)/8) ≤ (997964073301872549/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2137/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1538_exp_lower : (920114223292081063/1000000000000000000 : ℝ) ≤ Real.exp ((-2131390998873/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131390998873/3200000000000 : ℝ)/8) ≤ (115014277911510133/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131390998873/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1538_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745769461/50000000000 : ℝ) ≤ 4*Real.exp (8547/65536 : ℝ)*Real.exp (-mu (radius 8 (2137/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (102745769461/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2137/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1538_exp_radius
  have hrNumeric : (983828174967/1000000000000 : ℝ) ≤ Real.exp (-2137/131072 : ℝ) ∧ Real.exp (-2137/131072 : ℝ) ≤ (122978521871/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983828174967/1000000000000 : ℝ) ≤ (radius 8 (2137/16384 : ℝ)) ∧ (radius 8 (2137/16384 : ℝ)) ≤ (122978521871/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2137/16384 : ℝ)) (983828174967/1000000000000 : ℝ) (122978521871/125000000000 : ℝ) (89557414739/500000000000 : ℝ) (35822965897/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2137/16384 : ℝ)) (983828174967/1000000000000 : ℝ) (122978521871/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2137/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983828174967/1000000000000 : ℝ) (122978521871/125000000000 : ℝ) (991914087483/1000000000000 : ℝ) (247978521871/250000000000 : ℝ) (495940564727/500000000000 : ℝ) (198376225891/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2137/16384 : ℝ)) 1 (991914087483/1000000000000 : ℝ) (247978521871/250000000000 : ℝ) (495940564727/500000000000 : ℝ) (198376225891/200000000000 : ℝ) (247974402117/250000000000 : ℝ) (99189760847/100000000000 : ℝ) (991897608331/1000000000000 : ℝ) (991897608333/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2137/16384 : ℝ)) 2 (247974402117/250000000000 : ℝ) (99189760847/100000000000 : ℝ) (991897608331/1000000000000 : ℝ) (991897608333/1000000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2137/16384 : ℝ)) 3 (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2137/16384 : ℝ)) 4 (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2137/16384 : ℝ)) 5 (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2137/16384 : ℝ)) 6 (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2137/16384 : ℝ)) 7 (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2137/16384 : ℝ))) (89557414739/500000000000 : ℝ) (35822965897/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2137/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89557414739/500000000000 : ℝ) (35822965897/200000000000 : ℝ) (589557414739/1000000000000 : ℝ) (589557414743/1000000000000 : ℝ) (423219599591/1000000000000 : ℝ) (1058048999/2500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2137/16384 : ℝ))) 1 (589557414739/1000000000000 : ℝ) (589557414743/1000000000000 : ℝ) (423219599591/1000000000000 : ℝ) (1058048999/2500000000 : ℝ) (101277701433/200000000000 : ℝ) (126597126793/250000000000 : ℝ) (62439001859/125000000000 : ℝ) (3121950093/6250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2137/16384 : ℝ))) 2 (101277701433/200000000000 : ℝ) (126597126793/250000000000 : ℝ) (62439001859/125000000000 : ℝ) (3121950093/6250000000 : ℝ) (251475130509/500000000000 : ℝ) (251475130513/500000000000 : ℝ) (31433656793/62500000000 : ℝ) (502938508697/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2137/16384 : ℝ))) 3 (251475130509/500000000000 : ℝ) (251475130513/500000000000 : ℝ) (31433656793/62500000000 : ℝ) (502938508697/1000000000000 : ℝ) (502944384853/1000000000000 : ℝ) (251472192431/500000000000 : ℝ) (251472192409/500000000000 : ℝ) (125736096207/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2137/16384 : ℝ))) 4 (502944384853/1000000000000 : ℝ) (251472192431/500000000000 : ℝ) (251472192409/500000000000 : ℝ) (125736096207/250000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2137/16384 : ℝ))) 5 (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2137/16384 : ℝ))) 6 (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2137/16384 : ℝ))) 7 (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2137/16384 : ℝ)) hmem 8 (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2137/16384 : ℝ))) hcmem 8 (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2137/16384 : ℝ)) (991897608399/1000000000000 : ℝ) (495948804201/500000000000 : ℝ) (100588876967/200000000000 : ℝ) (100588876969/200000000000 : ℝ) (398238278623/500000000000 : ℝ) (159295311453/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1538_exp_lower
  have heNumeric : (102745769461/50000000000 : ℝ)/4 ≤ Real.exp (-2131390998873/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745769461/50000000000 : ℝ)/4 ≤ Real.exp ((8547/65536 : ℝ)-(159295311453/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8547/65536 : ℝ) (2137/16384 : ℝ) (159295311453/200000000000 : ℝ) (102745769461/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1539; no trusted numerical premise.
theorem cover8_leaf1539_exp_radius : (997963835368724561/1000000000000000000 : ℝ) ≤ Real.exp ((-8549/524288 : ℝ)/8) ∧ Real.exp ((-8549/524288 : ℝ)/8) ≤ (498981917684362281/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8549/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1539_exp_lower : (920114248687126151/1000000000000000000 : ℝ) ≤ Real.exp ((-532847573079/800000000000 : ℝ)/8) ∧ Real.exp ((-532847573079/800000000000 : ℝ)/8) ≤ (115014281085890769/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532847573079/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1539_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16054030023/7812500000 : ℝ) ≤ 4*Real.exp (2137/16384 : ℝ)*Real.exp (-mu (radius 8 (8549/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (16054030023/7812500000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8549/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1539_exp_radius
  have hrNumeric : (196765259693/200000000000 : ℝ) ≤ Real.exp (-8549/524288 : ℝ) ∧ Real.exp (-8549/524288 : ℝ) ≤ (491913149233/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196765259693/200000000000 : ℝ) ≤ (radius 8 (8549/65536 : ℝ)) ∧ (radius 8 (8549/65536 : ℝ)) ≤ (491913149233/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8549/65536 : ℝ)) (196765259693/200000000000 : ℝ) (491913149233/500000000000 : ℝ) (89562568139/500000000000 : ℝ) (44781284071/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8549/65536 : ℝ)) (196765259693/200000000000 : ℝ) (491913149233/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8549/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196765259693/200000000000 : ℝ) (491913149233/500000000000 : ℝ) (61994571827/62500000000 : ℝ) (991913149233/1000000000000 : ℝ) (495940091761/500000000000 : ℝ) (247970045881/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8549/65536 : ℝ)) 1 (61994571827/62500000000 : ℝ) (991913149233/1000000000000 : ℝ) (495940091761/500000000000 : ℝ) (247970045881/250000000000 : ℝ) (991896666377/1000000000000 : ℝ) (991896666379/1000000000000 : ℝ) (1549838541/1562500000 : ℝ) (495948333121/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8549/65536 : ℝ)) 2 (991896666377/1000000000000 : ℝ) (991896666379/1000000000000 : ℝ) (1549838541/1562500000 : ℝ) (495948333121/500000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8549/65536 : ℝ)) 3 (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8549/65536 : ℝ)) 4 (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8549/65536 : ℝ)) 5 (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8549/65536 : ℝ)) 6 (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8549/65536 : ℝ)) 7 (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8549/65536 : ℝ))) (89562568139/500000000000 : ℝ) (44781284071/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8549/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89562568139/500000000000 : ℝ) (44781284071/250000000000 : ℝ) (589562568139/1000000000000 : ℝ) (294781284071/500000000000 : ℝ) (423231776073/1000000000000 : ℝ) (423231776081/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8549/65536 : ℝ))) 1 (589562568139/1000000000000 : ℝ) (294781284071/500000000000 : ℝ) (423231776073/1000000000000 : ℝ) (423231776081/1000000000000 : ℝ) (253198586053/500000000000 : ℝ) (31649823257/62500000000 : ℝ) (249760691873/500000000000 : ℝ) (499521383753/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8549/65536 : ℝ))) 2 (253198586053/500000000000 : ℝ) (31649823257/62500000000 : ℝ) (249760691873/500000000000 : ℝ) (499521383753/1000000000000 : ℝ) (251479638963/500000000000 : ℝ) (502959277933/1000000000000 : ℝ) (125736882053/250000000000 : ℝ) (25147376411/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8549/65536 : ℝ))) 3 (251479638963/500000000000 : ℝ) (502959277933/1000000000000 : ℝ) (125736882053/250000000000 : ℝ) (25147376411/50000000000 : ℝ) (502953403069/1000000000000 : ℝ) (502953403077/1000000000000 : ℝ) (251476701517/500000000000 : ℝ) (502953403043/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8549/65536 : ℝ))) 4 (502953403069/1000000000000 : ℝ) (502953403077/1000000000000 : ℝ) (251476701517/500000000000 : ℝ) (502953403043/1000000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8549/65536 : ℝ))) 5 (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8549/65536 : ℝ))) 6 (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8549/65536 : ℝ))) 7 (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8549/65536 : ℝ)) hmem 8 (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8549/65536 : ℝ))) hcmem 8 (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8549/65536 : ℝ)) (247974166577/250000000000 : ℝ) (991896666311/1000000000000 : ℝ) (502953403051/1000000000000 : ℝ) (25147670153/50000000000 : ℝ) (398245797619/500000000000 : ℝ) (159298319051/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1539_exp_lower
  have heNumeric : (16054030023/7812500000 : ℝ)/4 ≤ Real.exp (-532847573079/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16054030023/7812500000 : ℝ)/4 ≤ Real.exp ((2137/16384 : ℝ)-(159298319051/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2137/16384 : ℝ) (8549/65536 : ℝ) (159298319051/200000000000 : ℝ) (16054030023/7812500000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1540; no trusted numerical premise.
theorem cover8_leaf1540_exp_radius : (997963597435633301/1000000000000000000 : ℝ) ≤ Real.exp ((-4275/262144 : ℝ)/8) ∧ Real.exp ((-4275/262144 : ℝ)/8) ≤ (498981798717816651/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4275/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1540_exp_lower : (184022854843899799/200000000000000000 : ℝ) ≤ Real.exp ((-10656947909691/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656947909691/16000000000000 : ℝ)/8) ≤ (230028568554874749/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656947909691/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1540_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054916299121/1000000000000 : ℝ) ≤ 4*Real.exp (8549/65536 : ℝ)*Real.exp (-mu (radius 8 (4275/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054916299121/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4275/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1540_exp_radius
  have hrNumeric : (983824421967/1000000000000 : ℝ) ≤ Real.exp (-4275/262144 : ℝ) ∧ Real.exp (-4275/262144 : ℝ) ≤ (61489026373/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983824421967/1000000000000 : ℝ) ≤ (radius 8 (4275/32768 : ℝ)) ∧ (radius 8 (4275/32768 : ℝ)) ≤ (61489026373/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4275/32768 : ℝ)) (983824421967/1000000000000 : ℝ) (61489026373/62500000000 : ℝ) (179135442443/1000000000000 : ℝ) (179135442449/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4275/32768 : ℝ)) (983824421967/1000000000000 : ℝ) (61489026373/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4275/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983824421967/1000000000000 : ℝ) (61489026373/62500000000 : ℝ) (991912210983/1000000000000 : ℝ) (123989026373/125000000000 : ℝ) (123984904699/125000000000 : ℝ) (991879237593/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4275/32768 : ℝ)) 1 (991912210983/1000000000000 : ℝ) (123989026373/125000000000 : ℝ) (123984904699/125000000000 : ℝ) (991879237593/1000000000000 : ℝ) (991895724287/1000000000000 : ℝ) (991895724289/1000000000000 : ℝ) (19837914483/20000000000 : ℝ) (123986965519/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4275/32768 : ℝ)) 2 (991895724287/1000000000000 : ℝ) (991895724289/1000000000000 : ℝ) (19837914483/20000000000 : ℝ) (123986965519/125000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4275/32768 : ℝ)) 3 (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4275/32768 : ℝ)) 4 (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4275/32768 : ℝ)) 5 (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4275/32768 : ℝ)) 6 (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4275/32768 : ℝ)) 7 (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4275/32768 : ℝ))) (179135442443/1000000000000 : ℝ) (179135442449/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4275/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179135442443/1000000000000 : ℝ) (179135442449/1000000000000 : ℝ) (589567721221/1000000000000 : ℝ) (23582708849/40000000000 : ℝ) (211621975727/500000000000 : ℝ) (211621975731/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4275/32768 : ℝ))) 1 (589567721221/1000000000000 : ℝ) (23582708849/40000000000 : ℝ) (211621975727/500000000000 : ℝ) (211621975731/500000000000 : ℝ) (506405836337/1000000000000 : ℝ) (63300729543/125000000000 : ℝ) (99906150357/200000000000 : ℝ) (31220671987/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4275/32768 : ℝ))) 2 (506405836337/1000000000000 : ℝ) (63300729543/125000000000 : ℝ) (99906150357/200000000000 : ℝ) (31220671987/62500000000 : ℝ) (502968294061/1000000000000 : ℝ) (125742073517/250000000000 : ℝ) (502956546963/1000000000000 : ℝ) (502956546971/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4275/32768 : ℝ))) 3 (502968294061/1000000000000 : ℝ) (125742073517/250000000000 : ℝ) (502956546963/1000000000000 : ℝ) (502956546971/1000000000000 : ℝ) (15717575641/31250000000 : ℝ) (12574060513/25000000000 : ℝ) (502962420477/1000000000000 : ℝ) (251481210243/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4275/32768 : ℝ))) 4 (15717575641/31250000000 : ℝ) (12574060513/25000000000 : ℝ) (502962420477/1000000000000 : ℝ) (251481210243/500000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4275/32768 : ℝ))) 5 (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4275/32768 : ℝ))) 6 (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4275/32768 : ℝ))) 7 (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4275/32768 : ℝ)) hmem 8 (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4275/32768 : ℝ))) hcmem 8 (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4275/32768 : ℝ)) (495947862109/500000000000 : ℝ) (991895724221/1000000000000 : ℝ) (251481210247/500000000000 : ℝ) (502962420503/1000000000000 : ℝ) (796506632033/1000000000000 : ℝ) (796506632051/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1540_exp_lower
  have heNumeric : (2054916299121/1000000000000 : ℝ)/4 ≤ Real.exp (-10656947909691/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054916299121/1000000000000 : ℝ)/4 ≤ Real.exp ((8549/65536 : ℝ)-(796506632051/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8549/65536 : ℝ) (4275/32768 : ℝ) (796506632051/1000000000000 : ℝ) (2054916299121/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1541; no trusted numerical premise.
theorem cover8_leaf1541_exp_radius : (997963359502598769/1000000000000000000 : ℝ) ≤ Real.exp ((-8551/524288 : ℝ)/8) ∧ Real.exp ((-8551/524288 : ℝ)/8) ≤ (99796335950259877/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8551/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1541_exp_lower : (57507143743067787/62500000000000000 : ℝ) ≤ Real.exp ((-5328472169357/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328472169357/8000000000000 : ℝ)/8) ≤ (920114299889084593/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328472169357/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1541_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (8219667031/4000000000 : ℝ) ≤ 4*Real.exp (4275/32768 : ℝ)*Real.exp (-mu (radius 8 (8551/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (8219667031/4000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8551/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1541_exp_radius
  have hrNumeric : (983822545473/1000000000000 : ℝ) ≤ Real.exp (-8551/524288 : ℝ) ∧ Real.exp (-8551/524288 : ℝ) ≤ (491911272737/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983822545473/1000000000000 : ℝ) ≤ (radius 8 (8551/65536 : ℝ)) ∧ (radius 8 (8551/65536 : ℝ)) ≤ (491911272737/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8551/65536 : ℝ)) (983822545473/1000000000000 : ℝ) (491911272737/500000000000 : ℝ) (179145747973/1000000000000 : ℝ) (8957287399/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8551/65536 : ℝ)) (983822545473/1000000000000 : ℝ) (491911272737/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8551/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983822545473/1000000000000 : ℝ) (491911272737/500000000000 : ℝ) (30997227273/31250000000 : ℝ) (991911272737/1000000000000 : ℝ) (991878291663/1000000000000 : ℝ) (61992393229/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8551/65536 : ℝ)) 1 (30997227273/31250000000 : ℝ) (991911272737/1000000000000 : ℝ) (991878291663/1000000000000 : ℝ) (61992393229/62500000000 : ℝ) (991894782199/1000000000000 : ℝ) (991894782201/1000000000000 : ℝ) (495947391031/500000000000 : ℝ) (61993423879/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8551/65536 : ℝ)) 2 (991894782199/1000000000000 : ℝ) (991894782201/1000000000000 : ℝ) (495947391031/500000000000 : ℝ) (61993423879/62500000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8551/65536 : ℝ)) 3 (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8551/65536 : ℝ)) 4 (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8551/65536 : ℝ)) 5 (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8551/65536 : ℝ)) 6 (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8551/65536 : ℝ)) 7 (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8551/65536 : ℝ))) (179145747973/1000000000000 : ℝ) (8957287399/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8551/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179145747973/1000000000000 : ℝ) (8957287399/50000000000 : ℝ) (294786436993/500000000000 : ℝ) (58957287399/100000000000 : ℝ) (84651225147/200000000000 : ℝ) (84651225149/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8551/65536 : ℝ))) 1 (294786436993/500000000000 : ℝ) (58957287399/100000000000 : ℝ) (84651225147/200000000000 : ℝ) (84651225149/200000000000 : ℝ) (25320724993/50000000000 : ℝ) (126603624967/250000000000 : ℝ) (499540118991/1000000000000 : ℝ) (499540118999/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8551/65536 : ℝ))) 2 (25320724993/50000000000 : ℝ) (126603624967/250000000000 : ℝ) (499540118991/1000000000000 : ℝ) (499540118999/1000000000000 : ℝ) (20119092377/40000000000 : ℝ) (251488654717/500000000000 : ℝ) (502965564943/1000000000000 : ℝ) (62870695619/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8551/65536 : ℝ))) 3 (20119092377/40000000000 : ℝ) (251488654717/500000000000 : ℝ) (502965564943/1000000000000 : ℝ) (62870695619/125000000000 : ℝ) (3929464353/7812500000 : ℝ) (502971437193/1000000000000 : ℝ) (502971437149/1000000000000 : ℝ) (502971437159/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8551/65536 : ℝ))) 4 (3929464353/7812500000 : ℝ) (502971437193/1000000000000 : ℝ) (502971437149/1000000000000 : ℝ) (502971437159/1000000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8551/65536 : ℝ))) 5 (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8551/65536 : ℝ))) 6 (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8551/65536 : ℝ))) 7 (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8551/65536 : ℝ)) hmem 8 (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8551/65536 : ℝ))) hcmem 8 (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8551/65536 : ℝ)) (99189478213/100000000000 : ℝ) (991894782133/1000000000000 : ℝ) (251485718583/500000000000 : ℝ) (62871429647/125000000000 : ℝ) (159304333527/200000000000 : ℝ) (398260833827/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1541_exp_lower
  have heNumeric : (8219667031/4000000000 : ℝ)/4 ≤ Real.exp (-5328472169357/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (8219667031/4000000000 : ℝ)/4 ≤ Real.exp ((4275/32768 : ℝ)-(398260833827/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4275/32768 : ℝ) (8551/65536 : ℝ) (398260833827/500000000000 : ℝ) (8219667031/4000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1542; no trusted numerical premise.
theorem cover8_leaf1542_exp_radius : (199592624313924193/200000000000000000 : ℝ) ≤ Real.exp ((-1069/65536 : ℝ)/8) ∧ Real.exp ((-1069/65536 : ℝ)/8) ≤ (498981560784810483/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1069/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1542_exp_lower : (230028581423798217/250000000000000000 : ℝ) ≤ Real.exp ((-2131388149749/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131388149749/3200000000000 : ℝ)/8) ≤ (920114325695192869/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131388149749/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1542_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027458609409/500000000000 : ℝ) ≤ 4*Real.exp (8551/65536 : ℝ)*Real.exp (-mu (radius 8 (1069/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027458609409/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1069/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1542_exp_radius
  have hrNumeric : (491910334491/500000000000 : ℝ) ≤ Real.exp (-1069/65536 : ℝ) ∧ Real.exp (-1069/65536 : ℝ) ≤ (983820668983/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491910334491/500000000000 : ℝ) ≤ (radius 8 (1069/8192 : ℝ)) ∧ (radius 8 (1069/8192 : ℝ)) ≤ (983820668983/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1069/8192 : ℝ)) (491910334491/500000000000 : ℝ) (983820668983/1000000000000 : ℝ) (1433248423/8000000000 : ℝ) (179156052881/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1069/8192 : ℝ)) (491910334491/500000000000 : ℝ) (983820668983/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1069/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491910334491/500000000000 : ℝ) (983820668983/1000000000000 : ℝ) (991910334491/1000000000000 : ℝ) (247977583623/250000000000 : ℝ) (495938672867/500000000000 : ℝ) (123984668217/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1069/8192 : ℝ)) 1 (991910334491/1000000000000 : ℝ) (247977583623/250000000000 : ℝ) (495938672867/500000000000 : ℝ) (123984668217/125000000000 : ℝ) (61993365007/62500000000 : ℝ) (495946920057/500000000000 : ℝ) (39675753599/40000000000 : ℝ) (991893839977/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1069/8192 : ℝ)) 2 (61993365007/62500000000 : ℝ) (495946920057/500000000000 : ℝ) (39675753599/40000000000 : ℝ) (991893839977/1000000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1069/8192 : ℝ)) 3 (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1069/8192 : ℝ)) 4 (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1069/8192 : ℝ)) 5 (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1069/8192 : ℝ)) 6 (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1069/8192 : ℝ)) 7 (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1069/8192 : ℝ))) (1433248423/8000000000 : ℝ) (179156052881/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1069/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1433248423/8000000000 : ℝ) (179156052881/1000000000000 : ℝ) (589578026437/1000000000000 : ℝ) (589578026441/1000000000000 : ℝ) (16930731957/40000000000 : ℝ) (423268298933/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1069/8192 : ℝ))) 1 (589578026437/1000000000000 : ℝ) (589578026441/1000000000000 : ℝ) (16930731957/40000000000 : ℝ) (423268298933/1000000000000 : ℝ) (506423162681/1000000000000 : ℝ) (506423162687/1000000000000 : ℝ) (49954948537/100000000000 : ℝ) (499549485377/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1069/8192 : ℝ))) 2 (506423162681/1000000000000 : ℝ) (506423162687/1000000000000 : ℝ) (49954948537/100000000000 : ℝ) (499549485377/1000000000000 : ℝ) (20119452961/40000000000 : ℝ) (7859161313/15625000000 : ℝ) (502974582157/1000000000000 : ℝ) (100594916433/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1069/8192 : ℝ))) 3 (20119452961/40000000000 : ℝ) (7859161313/15625000000 : ℝ) (502974582157/1000000000000 : ℝ) (100594916433/200000000000 : ℝ) (502980453091/1000000000000 : ℝ) (502980453099/1000000000000 : ℝ) (7859069579/15625000000 : ℝ) (100596090613/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1069/8192 : ℝ))) 4 (502980453091/1000000000000 : ℝ) (502980453099/1000000000000 : ℝ) (7859069579/15625000000 : ℝ) (100596090613/200000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1069/8192 : ℝ))) 5 (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1069/8192 : ℝ))) 6 (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1069/8192 : ℝ))) 7 (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1069/8192 : ℝ)) hmem 8 (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1069/8192 : ℝ))) hcmem 8 (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1069/8192 : ℝ)) (991893840043/1000000000000 : ℝ) (495946920023/500000000000 : ℝ) (502980453073/1000000000000 : ℝ) (251490226541/500000000000 : ℝ) (199134175513/250000000000 : ℝ) (79653670207/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1542_exp_lower
  have heNumeric : (1027458609409/500000000000 : ℝ)/4 ≤ Real.exp (-2131388149749/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027458609409/500000000000 : ℝ)/4 ≤ Real.exp ((8551/65536 : ℝ)-(79653670207/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8551/65536 : ℝ) (1069/8192 : ℝ) (79653670207/100000000000 : ℝ) (1027458609409/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1543; no trusted numerical premise.
theorem cover8_leaf1543_exp_radius : (62372680227293743/62500000000000000 : ℝ) ≤ Real.exp ((-8553/524288 : ℝ)/8) ∧ Real.exp ((-8553/524288 : ℝ)/8) ≤ (997962883636699889/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8553/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1543_exp_lower : (18402287032774879/20000000000000000 : ℝ) ≤ Real.exp ((-1332117142457/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332117142457/2000000000000 : ℝ)/8) ≤ (920114351638743951/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332117142457/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1543_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027458841171/500000000000 : ℝ) ≤ 4*Real.exp (1069/8192 : ℝ)*Real.exp (-mu (radius 8 (8553/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027458841171/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8553/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1543_exp_radius
  have hrNumeric : (196763758499/200000000000 : ℝ) ≤ Real.exp (-8553/524288 : ℝ) ∧ Real.exp (-8553/524288 : ℝ) ≤ (61488674531/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196763758499/200000000000 : ℝ) ≤ (radius 8 (8553/65536 : ℝ)) ∧ (radius 8 (8553/65536 : ℝ)) ≤ (61488674531/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8553/65536 : ℝ)) (196763758499/200000000000 : ℝ) (61488674531/62500000000 : ℝ) (89583178571/500000000000 : ℝ) (44791589287/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8553/65536 : ℝ)) (196763758499/200000000000 : ℝ) (61488674531/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8553/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196763758499/200000000000 : ℝ) (61488674531/62500000000 : ℝ) (991909396247/1000000000000 : ℝ) (123988674531/125000000000 : ℝ) (991876399807/1000000000000 : ℝ) (15498068747/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8553/65536 : ℝ)) 1 (991909396247/1000000000000 : ℝ) (123988674531/125000000000 : ℝ) (991876399807/1000000000000 : ℝ) (15498068747/15625000000 : ℝ) (991892898027/1000000000000 : ℝ) (247973224507/250000000000 : ℝ) (991892897889/1000000000000 : ℝ) (991892897891/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8553/65536 : ℝ)) 2 (991892898027/1000000000000 : ℝ) (247973224507/250000000000 : ℝ) (991892897889/1000000000000 : ℝ) (991892897891/1000000000000 : ℝ) (495946448979/500000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8553/65536 : ℝ)) 3 (495946448979/500000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8553/65536 : ℝ)) 4 (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8553/65536 : ℝ)) 5 (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8553/65536 : ℝ)) 6 (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8553/65536 : ℝ)) 7 (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8553/65536 : ℝ))) (89583178571/500000000000 : ℝ) (44791589287/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8553/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89583178571/500000000000 : ℝ) (44791589287/250000000000 : ℝ) (589583178571/1000000000000 : ℝ) (294791589287/500000000000 : ℝ) (211640235507/500000000000 : ℝ) (211640235511/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8553/65536 : ℝ))) 1 (589583178571/1000000000000 : ℝ) (294791589287/500000000000 : ℝ) (211640235507/500000000000 : ℝ) (211640235511/500000000000 : ℝ) (63303978099/125000000000 : ℝ) (253215912399/500000000000 : ℝ) (249779425457/500000000000 : ℝ) (499558850921/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8553/65536 : ℝ))) 2 (63303978099/125000000000 : ℝ) (253215912399/500000000000 : ℝ) (249779425457/500000000000 : ℝ) (499558850921/1000000000000 : ℝ) (502995337853/1000000000000 : ℝ) (25149766893/50000000000 : ℝ) (251491799299/500000000000 : ℝ) (251491799303/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8553/65536 : ℝ))) 3 (502995337853/1000000000000 : ℝ) (25149766893/50000000000 : ℝ) (251491799299/500000000000 : ℝ) (251491799303/500000000000 : ℝ) (20119578729/40000000000 : ℝ) (502989468233/1000000000000 : ℝ) (502989468191/1000000000000 : ℝ) (502989468199/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8553/65536 : ℝ))) 4 (20119578729/40000000000 : ℝ) (502989468233/1000000000000 : ℝ) (502989468191/1000000000000 : ℝ) (502989468199/1000000000000 : ℝ) (31436841763/62500000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8553/65536 : ℝ))) 5 (31436841763/62500000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8553/65536 : ℝ))) 6 (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8553/65536 : ℝ))) 7 (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8553/65536 : ℝ)) hmem 8 (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8553/65536 : ℝ))) hcmem 8 (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8553/65536 : ℝ)) (991892897957/1000000000000 : ℝ) (24797322449/25000000000 : ℝ) (502989468207/1000000000000 : ℝ) (62873683527/125000000000 : ℝ) (398275867637/500000000000 : ℝ) (796551735291/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1543_exp_lower
  have heNumeric : (1027458841171/500000000000 : ℝ)/4 ≤ Real.exp (-1332117142457/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027458841171/500000000000 : ℝ)/4 ≤ Real.exp ((1069/8192 : ℝ)-(796551735291/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1069/8192 : ℝ) (8553/65536 : ℝ) (796551735291/1000000000000 : ℝ) (1027458841171/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1544; no trusted numerical premise.
theorem cover8_leaf1544_exp_radius : (49898132285191777/50000000000000000 : ℝ) ≤ Real.exp ((-4277/262144 : ℝ)/8) ∧ Real.exp ((-4277/262144 : ℝ)/8) ≤ (997962645703835541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4277/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1544_exp_lower : (460057188859121331/500000000000000000 : ℝ) ≤ Real.exp ((-2131386702331/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131386702331/3200000000000 : ℝ)/8) ≤ (920114377718242663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131386702331/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1544_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027459074147/500000000000 : ℝ) ≤ 4*Real.exp (8553/65536 : ℝ)*Real.exp (-mu (radius 8 (4277/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027459074147/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4277/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1544_exp_radius
  have hrNumeric : (983816916011/1000000000000 : ℝ) ≤ Real.exp (-4277/262144 : ℝ) ∧ Real.exp (-4277/262144 : ℝ) ≤ (245954229003/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983816916011/1000000000000 : ℝ) ≤ (radius 8 (4277/32768 : ℝ)) ∧ (radius 8 (4277/32768 : ℝ)) ≤ (245954229003/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4277/32768 : ℝ)) (983816916011/1000000000000 : ℝ) (245954229003/250000000000 : ℝ) (179176660781/1000000000000 : ℝ) (179176660787/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4277/32768 : ℝ)) (983816916011/1000000000000 : ℝ) (245954229003/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4277/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983816916011/1000000000000 : ℝ) (245954229003/250000000000 : ℝ) (198381691601/200000000000 : ℝ) (495954229003/500000000000 : ℝ) (24796886347/25000000000 : ℝ) (495937726941/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4277/32768 : ℝ)) 1 (198381691601/200000000000 : ℝ) (495954229003/500000000000 : ℝ) (24796886347/25000000000 : ℝ) (495937726941/500000000000 : ℝ) (495945977971/500000000000 : ℝ) (123986494493/125000000000 : ℝ) (198378391161/200000000000 : ℝ) (991891955807/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4277/32768 : ℝ)) 2 (495945977971/500000000000 : ℝ) (123986494493/125000000000 : ℝ) (198378391161/200000000000 : ℝ) (991891955807/1000000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4277/32768 : ℝ)) 3 (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4277/32768 : ℝ)) 4 (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4277/32768 : ℝ)) 5 (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4277/32768 : ℝ)) 6 (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4277/32768 : ℝ)) 7 (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4277/32768 : ℝ))) (179176660781/1000000000000 : ℝ) (179176660787/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4277/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179176660781/1000000000000 : ℝ) (179176660787/1000000000000 : ℝ) (58958833039/100000000000 : ℝ) (294794165197/500000000000 : ℝ) (423292642011/1000000000000 : ℝ) (423292642019/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4277/32768 : ℝ))) 1 (58958833039/100000000000 : ℝ) (294794165197/500000000000 : ℝ) (423292642011/1000000000000 : ℝ) (423292642019/1000000000000 : ℝ) (2532202431/5000000000 : ℝ) (506440486207/1000000000000 : ℝ) (499568215631/1000000000000 : ℝ) (499568215639/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4277/32768 : ℝ))) 2 (2532202431/5000000000 : ℝ) (506440486207/1000000000000 : ℝ) (499568215631/1000000000000 : ℝ) (499568215639/1000000000000 : ℝ) (100600870183/200000000000 : ℝ) (503004350923/1000000000000 : ℝ) (251496307137/500000000000 : ℝ) (251496307141/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4277/32768 : ℝ))) 3 (100600870183/200000000000 : ℝ) (503004350923/1000000000000 : ℝ) (251496307137/500000000000 : ℝ) (251496307141/500000000000 : ℝ) (251499241297/500000000000 : ℝ) (502998482603/1000000000000 : ℝ) (785935129/1562500000 : ℝ) (502998482569/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4277/32768 : ℝ))) 4 (251499241297/500000000000 : ℝ) (502998482603/1000000000000 : ℝ) (785935129/1562500000 : ℝ) (502998482569/1000000000000 : ℝ) (502998482577/1000000000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4277/32768 : ℝ))) 5 (502998482577/1000000000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4277/32768 : ℝ))) 6 (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4277/32768 : ℝ))) 7 (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4277/32768 : ℝ)) hmem 8 (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4277/32768 : ℝ))) hcmem 8 (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4277/32768 : ℝ)) (991891955873/1000000000000 : ℝ) (247972988969/250000000000 : ℝ) (31437405161/62500000000 : ℝ) (251499241293/500000000000 : ℝ) (79656676731/100000000000 : ℝ) (79656676733/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1544_exp_lower
  have heNumeric : (1027459074147/500000000000 : ℝ)/4 ≤ Real.exp (-2131386702331/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027459074147/500000000000 : ℝ)/4 ≤ Real.exp ((8553/65536 : ℝ)-(79656676733/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8553/65536 : ℝ) (4277/32768 : ℝ) (79656676733/100000000000 : ℝ) (1027459074147/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1545; no trusted numerical premise.
theorem cover8_leaf1545_exp_radius : (498981203885513959/500000000000000000 : ℝ) ≤ Real.exp ((-8555/524288 : ℝ)/8) ∧ Real.exp ((-8555/524288 : ℝ)/8) ≤ (997962407771027919/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8555/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1545_exp_lower : (920114403935414231/1000000000000000000 : ℝ) ≤ Real.exp ((-5328464932251/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328464932251/8000000000000 : ℝ)/8) ≤ (115014300491926779/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328464932251/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1545_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054918616707/1000000000000 : ℝ) ≤ 4*Real.exp (4277/32768 : ℝ)*Real.exp (-mu (radius 8 (8555/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054918616707/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8555/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1545_exp_radius
  have hrNumeric : (983815039531/1000000000000 : ℝ) ≤ Real.exp (-8555/524288 : ℝ) ∧ Real.exp (-8555/524288 : ℝ) ≤ (245953759883/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983815039531/1000000000000 : ℝ) ≤ (radius 8 (8555/65536 : ℝ)) ∧ (radius 8 (8555/65536 : ℝ)) ≤ (245953759883/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8555/65536 : ℝ)) (983815039531/1000000000000 : ℝ) (245953759883/250000000000 : ℝ) (35837392757/200000000000 : ℝ) (179186963791/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8555/65536 : ℝ)) (983815039531/1000000000000 : ℝ) (245953759883/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8555/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983815039531/1000000000000 : ℝ) (245953759883/250000000000 : ℝ) (198381503953/200000000000 : ℝ) (495953759883/500000000000 : ℝ) (198374901591/200000000000 : ℝ) (247968626989/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8555/65536 : ℝ)) 1 (198381503953/200000000000 : ℝ) (495953759883/500000000000 : ℝ) (198374901591/200000000000 : ℝ) (247968626989/250000000000 : ℝ) (49594550693/50000000000 : ℝ) (991891013861/1000000000000 : ℝ) (495945506861/500000000000 : ℝ) (247972753431/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8555/65536 : ℝ)) 2 (49594550693/50000000000 : ℝ) (991891013861/1000000000000 : ℝ) (495945506861/500000000000 : ℝ) (247972753431/250000000000 : ℝ) (991891013791/1000000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8555/65536 : ℝ)) 3 (991891013791/1000000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8555/65536 : ℝ)) 4 (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8555/65536 : ℝ)) 5 (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8555/65536 : ℝ)) 6 (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8555/65536 : ℝ)) 7 (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8555/65536 : ℝ))) (35837392757/200000000000 : ℝ) (179186963791/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8555/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35837392757/200000000000 : ℝ) (179186963791/1000000000000 : ℝ) (147398370473/250000000000 : ℝ) (73699185237/125000000000 : ℝ) (105826202977/250000000000 : ℝ) (105826202979/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8555/65536 : ℝ))) 1 (147398370473/250000000000 : ℝ) (73699185237/125000000000 : ℝ) (105826202977/250000000000 : ℝ) (105826202979/250000000000 : ℝ) (5064491469/10000000000 : ℝ) (253224573453/500000000000 : ℝ) (99915515903/200000000000 : ℝ) (249788789761/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8555/65536 : ℝ))) 2 (5064491469/10000000000 : ℝ) (253224573453/500000000000 : ℝ) (99915515903/200000000000 : ℝ) (249788789761/500000000000 : ℝ) (503013363207/1000000000000 : ℝ) (251506681607/500000000000 : ℝ) (251500814589/500000000000 : ℝ) (100600325837/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8555/65536 : ℝ))) 3 (503013363207/1000000000000 : ℝ) (251506681607/500000000000 : ℝ) (251500814589/500000000000 : ℝ) (100600325837/200000000000 : ℝ) (245609129/488281250 : ℝ) (2515037481/5000000000 : ℝ) (251503748079/500000000000 : ℝ) (251503748083/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8555/65536 : ℝ))) 4 (245609129/488281250 : ℝ) (2515037481/5000000000 : ℝ) (251503748079/500000000000 : ℝ) (251503748083/500000000000 : ℝ) (20120299847/40000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8555/65536 : ℝ))) 5 (20120299847/40000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8555/65536 : ℝ))) 6 (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8555/65536 : ℝ))) 7 (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8555/65536 : ℝ)) hmem 8 (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8555/65536 : ℝ))) hcmem 8 (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8555/65536 : ℝ)) (99189101379/100000000000 : ℝ) (991891013793/1000000000000 : ℝ) (251503748087/500000000000 : ℝ) (503007496183/1000000000000 : ℝ) (398290899077/500000000000 : ℝ) (199145449543/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1545_exp_lower
  have heNumeric : (2054918616707/1000000000000 : ℝ)/4 ≤ Real.exp (-5328464932251/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054918616707/1000000000000 : ℝ)/4 ≤ Real.exp ((4277/32768 : ℝ)-(199145449543/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4277/32768 : ℝ) (8555/65536 : ℝ) (199145449543/250000000000 : ℝ) (2054918616707/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1546; no trusted numerical premise.
theorem cover8_leaf1546_exp_radius : (31186317807446157/31250000000000000 : ℝ) ≤ Real.exp ((-2139/131072 : ℝ)/8) ∧ Real.exp ((-2139/131072 : ℝ)/8) ≤ (39918486793531081/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2139/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1546_exp_lower : (920114430289568583/1000000000000000000 : ℝ) ≤ Real.exp ((-10656926198293/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656926198293/16000000000000 : ℝ)/8) ≤ (115014303786196073/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656926198293/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1546_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054919087567/1000000000000 : ℝ) ≤ 4*Real.exp (8555/65536 : ℝ)*Real.exp (-mu (radius 8 (2139/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054919087567/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2139/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1546_exp_radius
  have hrNumeric : (196762632611/200000000000 : ℝ) ≤ Real.exp (-2139/131072 : ℝ) ∧ Real.exp (-2139/131072 : ℝ) ≤ (61488322691/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196762632611/200000000000 : ℝ) ≤ (radius 8 (2139/16384 : ℝ)) ∧ (radius 8 (2139/16384 : ℝ)) ≤ (61488322691/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2139/16384 : ℝ)) (196762632611/200000000000 : ℝ) (61488322691/62500000000 : ℝ) (35839453231/200000000000 : ℝ) (89598633081/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2139/16384 : ℝ)) (196762632611/200000000000 : ℝ) (61488322691/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2139/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196762632611/200000000000 : ℝ) (61488322691/62500000000 : ℝ) (991906581527/1000000000000 : ℝ) (123988322691/125000000000 : ℝ) (99187356203/100000000000 : ℝ) (991873562031/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2139/16384 : ℝ)) 1 (991906581527/1000000000000 : ℝ) (123988322691/125000000000 : ℝ) (99187356203/100000000000 : ℝ) (991873562031/1000000000000 : ℝ) (495945035889/500000000000 : ℝ) (49594503589/50000000000 : ℝ) (991890071641/1000000000000 : ℝ) (991890071643/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2139/16384 : ℝ)) 2 (495945035889/500000000000 : ℝ) (49594503589/50000000000 : ℝ) (991890071641/1000000000000 : ℝ) (991890071643/1000000000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2139/16384 : ℝ)) 3 (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2139/16384 : ℝ)) 4 (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2139/16384 : ℝ)) 5 (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2139/16384 : ℝ)) 6 (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2139/16384 : ℝ)) 7 (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2139/16384 : ℝ))) (35839453231/200000000000 : ℝ) (89598633081/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2139/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35839453231/200000000000 : ℝ) (89598633081/500000000000 : ℝ) (589598633077/1000000000000 : ℝ) (589598633081/1000000000000 : ℝ) (423316980707/1000000000000 : ℝ) (105829245179/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2139/16384 : ℝ))) 1 (589598633077/1000000000000 : ℝ) (589598633081/1000000000000 : ℝ) (423316980707/1000000000000 : ℝ) (105829245179/250000000000 : ℝ) (126614451723/250000000000 : ℝ) (506457806899/1000000000000 : ℝ) (249793471283/500000000000 : ℝ) (249793471287/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2139/16384 : ℝ))) 2 (126614451723/250000000000 : ℝ) (506457806899/1000000000000 : ℝ) (249793471283/500000000000 : ℝ) (249793471287/500000000000 : ℝ) (503022374729/1000000000000 : ℝ) (503022374737/1000000000000 : ℝ) (50301064331/100000000000 : ℝ) (503010643319/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2139/16384 : ℝ))) 3 (503022374729/1000000000000 : ℝ) (503022374737/1000000000000 : ℝ) (50301064331/100000000000 : ℝ) (503010643319/1000000000000 : ℝ) (503016509019/1000000000000 : ℝ) (125754127257/250000000000 : ℝ) (100603301797/200000000000 : ℝ) (251508254497/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2139/16384 : ℝ))) 4 (503016509019/1000000000000 : ℝ) (125754127257/250000000000 : ℝ) (100603301797/200000000000 : ℝ) (251508254497/500000000000 : ℝ) (251508254501/500000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2139/16384 : ℝ))) 5 (251508254501/500000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2139/16384 : ℝ))) 6 (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2139/16384 : ℝ))) 7 (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2139/16384 : ℝ)) hmem 8 (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2139/16384 : ℝ))) hcmem 8 (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2139/16384 : ℝ)) (991890071709/1000000000000 : ℝ) (30996564741/31250000000 : ℝ) (503016509001/1000000000000 : ℝ) (503016509011/1000000000000 : ℝ) (796596827803/1000000000000 : ℝ) (796596827823/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1546_exp_lower
  have heNumeric : (2054919087567/1000000000000 : ℝ)/4 ≤ Real.exp (-10656926198293/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054919087567/1000000000000 : ℝ)/4 ≤ Real.exp ((8555/65536 : ℝ)-(796596827823/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8555/65536 : ℝ) (2139/16384 : ℝ) (796596827823/1000000000000 : ℝ) (2054919087567/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1547; no trusted numerical premise.
theorem cover8_leaf1547_exp_radius : (498980965952791429/500000000000000000 : ℝ) ≤ Real.exp ((-8557/524288 : ℝ)/8) ∧ Real.exp ((-8557/524288 : ℝ)/8) ≤ (997961931905582859/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8557/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1547_exp_lower : (460057228390065329/500000000000000000 : ℝ) ≤ Real.exp ((-2664230628277/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664230628277/4000000000000 : ℝ)/8) ≤ (920114456780130659/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664230628277/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1547_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64216236277/31250000000 : ℝ) ≤ 4*Real.exp (2139/16384 : ℝ)*Real.exp (-mu (radius 8 (8557/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (64216236277/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8557/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1547_exp_radius
  have hrNumeric : (491905643291/500000000000 : ℝ) ≤ Real.exp (-8557/524288 : ℝ) ∧ Real.exp (-8557/524288 : ℝ) ≤ (983811286583/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491905643291/500000000000 : ℝ) ≤ (radius 8 (8557/65536 : ℝ)) ∧ (radius 8 (8557/65536 : ℝ)) ≤ (983811286583/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8557/65536 : ℝ)) (491905643291/500000000000 : ℝ) (983811286583/1000000000000 : ℝ) (179207567897/1000000000000 : ℝ) (5600236497/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8557/65536 : ℝ)) (491905643291/500000000000 : ℝ) (983811286583/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8557/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491905643291/500000000000 : ℝ) (983811286583/1000000000000 : ℝ) (991905643291/1000000000000 : ℝ) (247976410823/250000000000 : ℝ) (495936308053/500000000000 : ℝ) (247968154027/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8557/65536 : ℝ)) 1 (991905643291/1000000000000 : ℝ) (247976410823/250000000000 : ℝ) (495936308053/500000000000 : ℝ) (247968154027/250000000000 : ℝ) (495944564849/500000000000 : ℝ) (9918891297/10000000000 : ℝ) (991889129561/1000000000000 : ℝ) (991889129563/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8557/65536 : ℝ)) 2 (495944564849/500000000000 : ℝ) (9918891297/10000000000 : ℝ) (991889129561/1000000000000 : ℝ) (991889129563/1000000000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8557/65536 : ℝ)) 3 (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8557/65536 : ℝ)) 4 (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8557/65536 : ℝ)) 5 (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8557/65536 : ℝ)) 6 (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8557/65536 : ℝ)) 7 (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8557/65536 : ℝ))) (179207567897/1000000000000 : ℝ) (5600236497/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8557/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179207567897/1000000000000 : ℝ) (5600236497/31250000000 : ℝ) (147400945987/250000000000 : ℝ) (36850236497/62500000000 : ℝ) (211664574207/500000000000 : ℝ) (423329148423/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8557/65536 : ℝ))) 1 (147400945987/250000000000 : ℝ) (36850236497/62500000000 : ℝ) (211664574207/500000000000 : ℝ) (423329148423/1000000000000 : ℝ) (506466466181/1000000000000 : ℝ) (126616616547/250000000000 : ℝ) (49959630479/100000000000 : ℝ) (249798152399/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8557/65536 : ℝ))) 2 (506466466181/1000000000000 : ℝ) (126616616547/250000000000 : ℝ) (49959630479/100000000000 : ℝ) (249798152399/500000000000 : ℝ) (100606277097/200000000000 : ℝ) (503031385493/1000000000000 : ℝ) (503019656677/1000000000000 : ℝ) (251509828343/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8557/65536 : ℝ))) 3 (100606277097/200000000000 : ℝ) (503031385493/1000000000000 : ℝ) (503019656677/1000000000000 : ℝ) (251509828343/500000000000 : ℝ) (503025521081/1000000000000 : ℝ) (50302552109/100000000000 : ℝ) (251512760523/500000000000 : ℝ) (15719547533/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8557/65536 : ℝ))) 4 (503025521081/1000000000000 : ℝ) (50302552109/100000000000 : ℝ) (251512760523/500000000000 : ℝ) (15719547533/31250000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8557/65536 : ℝ))) 5 (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8557/65536 : ℝ))) 6 (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8557/65536 : ℝ))) 7 (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8557/65536 : ℝ)) hmem 8 (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8557/65536 : ℝ))) hcmem 8 (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8557/65536 : ℝ)) (991889129629/1000000000000 : ℝ) (30996535301/31250000000 : ℝ) (503025521063/1000000000000 : ℝ) (503025521073/1000000000000 : ℝ) (796611856269/1000000000000 : ℝ) (24894120509/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1547_exp_lower
  have heNumeric : (64216236277/31250000000 : ℝ)/4 ≤ Real.exp (-2664230628277/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64216236277/31250000000 : ℝ)/4 ≤ Real.exp ((2139/16384 : ℝ)-(24894120509/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2139/16384 : ℝ) (8557/65536 : ℝ) (24894120509/31250000000 : ℝ) (64216236277/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1548; no trusted numerical premise.
theorem cover8_leaf1548_exp_radius : (49898084698647271/50000000000000000 : ℝ) ≤ Real.exp ((-4279/262144 : ℝ)/8) ∧ Real.exp ((-4279/262144 : ℝ)/8) ≤ (997961693972945421/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4279/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1548_exp_lower : (36804579336270217/40000000000000000 : ℝ) ≤ Real.exp ((-2131383761799/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131383761799/3200000000000 : ℝ)/8) ≤ (460057241703377713/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131383761799/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1548_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054920036593/1000000000000 : ℝ) ≤ 4*Real.exp (8557/65536 : ℝ)*Real.exp (-mu (radius 8 (4279/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054920036593/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4279/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1548_exp_radius
  have hrNumeric : (15372022033/15625000000 : ℝ) ≤ Real.exp (-4279/262144 : ℝ) ∧ Real.exp (-4279/262144 : ℝ) ≤ (983809410113/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15372022033/15625000000 : ℝ) ≤ (radius 8 (4279/32768 : ℝ)) ∧ (radius 8 (4279/32768 : ℝ)) ≤ (983809410113/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4279/32768 : ℝ)) (15372022033/15625000000 : ℝ) (983809410113/1000000000000 : ℝ) (179217869011/1000000000000 : ℝ) (89608934509/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4279/32768 : ℝ)) (15372022033/15625000000 : ℝ) (983809410113/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4279/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15372022033/15625000000 : ℝ) (983809410113/1000000000000 : ℝ) (30997022033/31250000000 : ℝ) (991904705057/1000000000000 : ℝ) (991871670183/1000000000000 : ℝ) (123983958773/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4279/32768 : ℝ)) 1 (30997022033/31250000000 : ℝ) (991904705057/1000000000000 : ℝ) (991871670183/1000000000000 : ℝ) (123983958773/125000000000 : ℝ) (991888187619/1000000000000 : ℝ) (991888187621/1000000000000 : ℝ) (991888187481/1000000000000 : ℝ) (991888187483/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4279/32768 : ℝ)) 2 (991888187619/1000000000000 : ℝ) (991888187621/1000000000000 : ℝ) (991888187481/1000000000000 : ℝ) (991888187483/1000000000000 : ℝ) (19837763751/20000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4279/32768 : ℝ)) 3 (19837763751/20000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4279/32768 : ℝ)) 4 (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4279/32768 : ℝ)) 5 (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4279/32768 : ℝ)) 6 (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4279/32768 : ℝ)) 7 (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4279/32768 : ℝ))) (179217869011/1000000000000 : ℝ) (89608934509/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4279/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (179217869011/1000000000000 : ℝ) (89608934509/500000000000 : ℝ) (117921786901/200000000000 : ℝ) (589608934509/1000000000000 : ℝ) (423341315029/1000000000000 : ℝ) (211670657519/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4279/32768 : ℝ))) 1 (117921786901/200000000000 : ℝ) (589608934509/1000000000000 : ℝ) (423341315029/1000000000000 : ℝ) (211670657519/500000000000 : ℝ) (506475124767/1000000000000 : ℝ) (253237562387/500000000000 : ℝ) (499605666187/1000000000000 : ℝ) (99921133239/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4279/32768 : ℝ))) 2 (506475124767/1000000000000 : ℝ) (253237562387/500000000000 : ℝ) (499605666187/1000000000000 : ℝ) (99921133239/200000000000 : ℝ) (503040395477/1000000000000 : ℝ) (100608079097/200000000000 : ℝ) (251514334639/500000000000 : ℝ) (503028669287/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4279/32768 : ℝ))) 3 (503040395477/1000000000000 : ℝ) (100608079097/200000000000 : ℝ) (251514334639/500000000000 : ℝ) (503028669287/1000000000000 : ℝ) (503034532377/1000000000000 : ℝ) (251517266193/500000000000 : ℝ) (503034532343/1000000000000 : ℝ) (982489321/1953125000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4279/32768 : ℝ))) 4 (503034532377/1000000000000 : ℝ) (251517266193/500000000000 : ℝ) (503034532343/1000000000000 : ℝ) (982489321/1953125000 : ℝ) (12575863309/25000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4279/32768 : ℝ))) 5 (12575863309/25000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4279/32768 : ℝ))) 6 (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4279/32768 : ℝ))) 7 (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4279/32768 : ℝ)) hmem 8 (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4279/32768 : ℝ))) hcmem 8 (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4279/32768 : ℝ)) (991888187549/1000000000000 : ℝ) (30996505861/31250000000 : ℝ) (503034532359/1000000000000 : ℝ) (503034532369/1000000000000 : ℝ) (15932537671/20000000000 : ℝ) (79662688357/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1548_exp_lower
  have heNumeric : (2054920036593/1000000000000 : ℝ)/4 ≤ Real.exp (-2131383761799/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054920036593/1000000000000 : ℝ)/4 ≤ Real.exp ((8557/65536 : ℝ)-(79662688357/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8557/65536 : ℝ) (4279/32768 : ℝ) (79662688357/100000000000 : ℝ) (2054920036593/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1549; no trusted numerical premise.
theorem cover8_leaf1549_exp_radius : (997961456040364709/1000000000000000000 : ℝ) ≤ Real.exp ((-8559/524288 : ℝ)/8) ∧ Real.exp ((-8559/524288 : ℝ)/8) ≤ (99796145604036471/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8559/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1549_exp_lower : (230028627542964549/250000000000000000 : ℝ) ≤ Real.exp ((-5328457542809/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328457542809/8000000000000 : ℝ)/8) ≤ (920114510171858197/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328457542809/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1549_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513730128699/250000000000 : ℝ) ≤ 4*Real.exp (4279/32768 : ℝ)*Real.exp (-mu (radius 8 (8559/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513730128699/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8559/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1549_exp_radius
  have hrNumeric : (983807533647/1000000000000 : ℝ) ≤ Real.exp (-8559/524288 : ℝ) ∧ Real.exp (-8559/524288 : ℝ) ≤ (61487970853/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983807533647/1000000000000 : ℝ) ≤ (radius 8 (8559/65536 : ℝ)) ∧ (radius 8 (8559/65536 : ℝ)) ≤ (61487970853/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8559/65536 : ℝ)) (983807533647/1000000000000 : ℝ) (61487970853/62500000000 : ℝ) (89614084743/500000000000 : ℝ) (44807042373/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8559/65536 : ℝ)) (983807533647/1000000000000 : ℝ) (61487970853/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8559/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983807533647/1000000000000 : ℝ) (61487970853/62500000000 : ℝ) (991903766823/1000000000000 : ℝ) (123987970853/125000000000 : ℝ) (991870724261/1000000000000 : ℝ) (495935362131/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8559/65536 : ℝ)) 1 (991903766823/1000000000000 : ℝ) (123987970853/125000000000 : ℝ) (991870724261/1000000000000 : ℝ) (495935362131/500000000000 : ℝ) (495943622771/500000000000 : ℝ) (991887245543/1000000000000 : ℝ) (247971811351/250000000000 : ℝ) (495943622703/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8559/65536 : ℝ)) 2 (495943622771/500000000000 : ℝ) (991887245543/1000000000000 : ℝ) (247971811351/250000000000 : ℝ) (495943622703/500000000000 : ℝ) (991887245473/1000000000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8559/65536 : ℝ)) 3 (991887245473/1000000000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8559/65536 : ℝ)) 4 (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8559/65536 : ℝ)) 5 (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8559/65536 : ℝ)) 6 (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8559/65536 : ℝ)) 7 (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8559/65536 : ℝ))) (89614084743/500000000000 : ℝ) (44807042373/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8559/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89614084743/500000000000 : ℝ) (44807042373/250000000000 : ℝ) (589614084743/1000000000000 : ℝ) (294807042373/500000000000 : ℝ) (21167674027/50000000000 : ℝ) (105838370137/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8559/65536 : ℝ))) 1 (589614084743/1000000000000 : ℝ) (294807042373/500000000000 : ℝ) (21167674027/50000000000 : ℝ) (105838370137/250000000000 : ℝ) (506483782641/1000000000000 : ℝ) (506483782647/1000000000000 : ℝ) (249807513373/500000000000 : ℝ) (499615026753/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8559/65536 : ℝ))) 2 (506483782641/1000000000000 : ℝ) (506483782647/1000000000000 : ℝ) (249807513373/500000000000 : ℝ) (499615026753/1000000000000 : ℝ) (503049404693/1000000000000 : ℝ) (5030494047/10000000000 : ℝ) (31439855069/62500000000 : ℝ) (503037681111/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8559/65536 : ℝ))) 3 (503049404693/1000000000000 : ℝ) (5030494047/10000000000 : ℝ) (31439855069/62500000000 : ℝ) (503037681111/1000000000000 : ℝ) (251521771449/500000000000 : ℝ) (251521771453/500000000000 : ℝ) (31440221429/62500000000 : ℝ) (62880442859/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8559/65536 : ℝ))) 4 (251521771449/500000000000 : ℝ) (251521771453/500000000000 : ℝ) (31440221429/62500000000 : ℝ) (62880442859/125000000000 : ℝ) (503043542881/1000000000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8559/65536 : ℝ))) 5 (503043542881/1000000000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8559/65536 : ℝ))) 6 (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8559/65536 : ℝ))) 7 (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8559/65536 : ℝ)) hmem 8 (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8559/65536 : ℝ))) hcmem 8 (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8559/65536 : ℝ)) (30996476421/31250000000 : ℝ) (39675489819/40000000000 : ℝ) (3144022143/6250000000 : ℝ) (503043542889/1000000000000 : ℝ) (79664190963/100000000000 : ℝ) (49790119353/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1549_exp_lower
  have heNumeric : (513730128699/250000000000 : ℝ)/4 ≤ Real.exp (-5328457542809/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513730128699/250000000000 : ℝ)/4 ≤ Real.exp ((4279/32768 : ℝ)-(49790119353/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4279/32768 : ℝ) (8559/65536 : ℝ) (49790119353/62500000000 : ℝ) (513730128699/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1525_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1525_certificate
#check SmaleRate.Proofs.cover8_leaf1526_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1526_certificate
#check SmaleRate.Proofs.cover8_leaf1527_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1527_certificate
#check SmaleRate.Proofs.cover8_leaf1528_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1528_certificate
#check SmaleRate.Proofs.cover8_leaf1529_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1529_certificate
#check SmaleRate.Proofs.cover8_leaf1530_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1530_certificate
#check SmaleRate.Proofs.cover8_leaf1531_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1531_certificate
#check SmaleRate.Proofs.cover8_leaf1532_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1532_certificate
#check SmaleRate.Proofs.cover8_leaf1533_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1533_certificate
#check SmaleRate.Proofs.cover8_leaf1534_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1534_certificate
#check SmaleRate.Proofs.cover8_leaf1535_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1535_certificate
#check SmaleRate.Proofs.cover8_leaf1536_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1536_certificate
#check SmaleRate.Proofs.cover8_leaf1537_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1537_certificate
#check SmaleRate.Proofs.cover8_leaf1538_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1538_certificate
#check SmaleRate.Proofs.cover8_leaf1539_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1539_certificate
#check SmaleRate.Proofs.cover8_leaf1540_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1540_certificate
#check SmaleRate.Proofs.cover8_leaf1541_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1541_certificate
#check SmaleRate.Proofs.cover8_leaf1542_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1542_certificate
#check SmaleRate.Proofs.cover8_leaf1543_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1543_certificate
#check SmaleRate.Proofs.cover8_leaf1544_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1544_certificate
#check SmaleRate.Proofs.cover8_leaf1545_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1545_certificate
#check SmaleRate.Proofs.cover8_leaf1546_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1546_certificate
#check SmaleRate.Proofs.cover8_leaf1547_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1547_certificate
#check SmaleRate.Proofs.cover8_leaf1548_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1548_certificate
#check SmaleRate.Proofs.cover8_leaf1549_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1549_certificate
