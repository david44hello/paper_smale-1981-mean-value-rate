/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0075; no trusted numerical premise.
theorem cover8_leaf0075_exp_radius : (49905389764423487/50000000000000000 : ℝ) ≤ Real.exp ((-993/65536 : ℝ)/8) ∧ Real.exp ((-993/65536 : ℝ)/8) ≤ (998107795288469741/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-993/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0075_exp_lower : (920119743048567057/1000000000000000000 : ℝ) ≤ Real.exp ((-2664046781471/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664046781471/4000000000000 : ℝ)/8) ≤ (460059871524283529/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664046781471/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0075_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027507005317/500000000000 : ℝ) ≤ 4*Real.exp (1985/16384 : ℝ)*Real.exp (-mu (radius 8 (993/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027507005317/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (993/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0075_exp_radius
  have hrNumeric : (98496223609/100000000000 : ℝ) ≤ Real.exp (-993/65536 : ℝ) ∧ Real.exp (-993/65536 : ℝ) ≤ (984962236091/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98496223609/100000000000 : ℝ) ≤ (radius 8 (993/8192 : ℝ)) ∧ (radius 8 (993/8192 : ℝ)) ≤ (984962236091/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (993/8192 : ℝ)) (98496223609/100000000000 : ℝ) (984962236091/1000000000000 : ℝ) (172769770141/1000000000000 : ℝ) (172769770147/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (993/8192 : ℝ)) (98496223609/100000000000 : ℝ) (984962236091/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (993/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98496223609/100000000000 : ℝ) (984962236091/1000000000000 : ℝ) (198496223609/200000000000 : ℝ) (496240559023/500000000000 : ℝ) (496226318349/500000000000 : ℝ) (9924526367/10000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (993/8192 : ℝ)) 1 (198496223609/200000000000 : ℝ) (496240559023/500000000000 : ℝ) (496226318349/500000000000 : ℝ) (9924526367/10000000000 : ℝ) (992466877371/1000000000000 : ℝ) (992466877373/1000000000000 : ℝ) (992466877269/1000000000000 : ℝ) (992466877271/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (993/8192 : ℝ)) 2 (992466877371/1000000000000 : ℝ) (992466877373/1000000000000 : ℝ) (992466877269/1000000000000 : ℝ) (992466877271/1000000000000 : ℝ) (24811671933/25000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (993/8192 : ℝ)) 3 (24811671933/25000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (993/8192 : ℝ)) 4 (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (993/8192 : ℝ)) 5 (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (993/8192 : ℝ)) 6 (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (993/8192 : ℝ)) 7 (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (993/8192 : ℝ))) (172769770141/1000000000000 : ℝ) (172769770147/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (993/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172769770141/1000000000000 : ℝ) (172769770147/1000000000000 : ℝ) (58638488507/100000000000 : ℝ) (293192442537/500000000000 : ℝ) (103913957839/250000000000 : ℝ) (83131166273/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (993/8192 : ℝ))) 1 (58638488507/100000000000 : ℝ) (293192442537/500000000000 : ℝ) (103913957839/250000000000 : ℝ) (83131166273/200000000000 : ℝ) (501020358213/1000000000000 : ℝ) (25051017911/50000000000 : ℝ) (493694538047/1000000000000 : ℝ) (98738907611/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (993/8192 : ℝ))) 2 (501020358213/1000000000000 : ℝ) (25051017911/50000000000 : ℝ) (493694538047/1000000000000 : ℝ) (98738907611/200000000000 : ℝ) (49735744813/100000000000 : ℝ) (248678724069/500000000000 : ℝ) (1989375839/4000000000 : ℝ) (248671979879/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (993/8192 : ℝ))) 3 (49735744813/100000000000 : ℝ) (248678724069/500000000000 : ℝ) (1989375839/4000000000 : ℝ) (248671979879/500000000000 : ℝ) (24867535197/50000000000 : ℝ) (124337675987/250000000000 : ℝ) (248675351947/500000000000 : ℝ) (497350703903/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (993/8192 : ℝ))) 4 (24867535197/50000000000 : ℝ) (124337675987/250000000000 : ℝ) (248675351947/500000000000 : ℝ) (497350703903/1000000000000 : ℝ) (497350703917/1000000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (993/8192 : ℝ))) 5 (497350703917/1000000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (993/8192 : ℝ))) 6 (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (993/8192 : ℝ))) 7 (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (993/8192 : ℝ)) hmem 8 (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (993/8192 : ℝ))) hcmem 8 (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (993/8192 : ℝ)) (992466877319/1000000000000 : ℝ) (496233438661/500000000000 : ℝ) (124337675979/250000000000 : ℝ) (248675351963/500000000000 : ℝ) (157433296101/200000000000 : ℝ) (196791620131/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0075_exp_lower
  have heNumeric : (1027507005317/500000000000 : ℝ)/4 ≤ Real.exp (-2664046781471/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027507005317/500000000000 : ℝ)/4 ≤ Real.exp ((1985/16384 : ℝ)-(196791620131/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1985/16384 : ℝ) (993/8192 : ℝ) (196791620131/250000000000 : ℝ) (1027507005317/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0076; no trusted numerical premise.
theorem cover8_leaf0076_exp_radius : (62381677713697141/62500000000000000 : ℝ) ≤ Real.exp ((-1987/131072 : ℝ)/8) ∧ Real.exp ((-1987/131072 : ℝ)/8) ≤ (998106843419154257/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1987/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0076_exp_lower : (920119492578349063/1000000000000000000 : ℝ) ≤ Real.exp ((-1332027746173/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332027746173/2000000000000 : ℝ)/8) ≤ (115014936572293633/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332027746173/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0076_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055009535397/1000000000000 : ℝ) ≤ 4*Real.exp (993/8192 : ℝ)*Real.exp (-mu (radius 8 (1987/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2055009535397/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1987/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0076_exp_radius
  have hrNumeric : (492477360727/500000000000 : ℝ) ≤ Real.exp (-1987/131072 : ℝ) ∧ Real.exp (-1987/131072 : ℝ) ≤ (196990944291/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492477360727/500000000000 : ℝ) ≤ (radius 8 (1987/16384 : ℝ)) ∧ (radius 8 (1987/16384 : ℝ)) ≤ (196990944291/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1987/16384 : ℝ)) (492477360727/500000000000 : ℝ) (196990944291/200000000000 : ℝ) (43203151421/250000000000 : ℝ) (172812605691/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1987/16384 : ℝ)) (492477360727/500000000000 : ℝ) (196990944291/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1987/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492477360727/500000000000 : ℝ) (196990944291/200000000000 : ℝ) (992477360727/1000000000000 : ℝ) (124059670091/125000000000 : ℝ) (992448850799/1000000000000 : ℝ) (992448850801/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1987/16384 : ℝ)) 1 (992477360727/1000000000000 : ℝ) (124059670091/125000000000 : ℝ) (992448850799/1000000000000 : ℝ) (992448850801/1000000000000 : ℝ) (992463105763/1000000000000 : ℝ) (198492621153/200000000000 : ℝ) (49623155283/50000000000 : ℝ) (992463105663/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1987/16384 : ℝ)) 2 (992463105763/1000000000000 : ℝ) (198492621153/200000000000 : ℝ) (49623155283/50000000000 : ℝ) (992463105663/1000000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1987/16384 : ℝ)) 3 (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1987/16384 : ℝ)) 4 (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1987/16384 : ℝ)) 5 (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1987/16384 : ℝ)) 6 (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1987/16384 : ℝ)) 7 (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1987/16384 : ℝ))) (43203151421/250000000000 : ℝ) (172812605691/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1987/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43203151421/250000000000 : ℝ) (172812605691/1000000000000 : ℝ) (293203151421/500000000000 : ℝ) (293203151423/500000000000 : ℝ) (415707355821/1000000000000 : ℝ) (41570735583/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1987/16384 : ℝ))) 1 (293203151421/500000000000 : ℝ) (293203151423/500000000000 : ℝ) (415707355821/1000000000000 : ℝ) (41570735583/100000000000 : ℝ) (501056829331/1000000000000 : ℝ) (250528414669/500000000000 : ℝ) (493734152749/1000000000000 : ℝ) (493734152757/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1987/16384 : ℝ))) 2 (501056829331/1000000000000 : ℝ) (250528414669/500000000000 : ℝ) (493734152749/1000000000000 : ℝ) (493734152757/1000000000000 : ℝ) (3108721819/6250000000 : ℝ) (62174436381/125000000000 : ℝ) (15543187977/31250000000 : ℝ) (497382015273/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1987/16384 : ℝ))) 3 (3108721819/6250000000 : ℝ) (62174436381/125000000000 : ℝ) (15543187977/31250000000 : ℝ) (497382015273/1000000000000 : ℝ) (1942924817/3906250000 : ℝ) (497388753161/1000000000000 : ℝ) (248694376553/500000000000 : ℝ) (99477750623/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1987/16384 : ℝ))) 4 (1942924817/3906250000 : ℝ) (497388753161/1000000000000 : ℝ) (248694376553/500000000000 : ℝ) (99477750623/200000000000 : ℝ) (497388753129/1000000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1987/16384 : ℝ))) 5 (497388753129/1000000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1987/16384 : ℝ))) 6 (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1987/16384 : ℝ))) 7 (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1987/16384 : ℝ)) hmem 8 (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1987/16384 : ℝ))) hcmem 8 (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1987/16384 : ℝ)) (992463105711/1000000000000 : ℝ) (496231552857/500000000000 : ℝ) (62173594141/125000000000 : ℝ) (248694376569/500000000000 : ℝ) (39361484669/50000000000 : ℝ) (787229693399/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0076_exp_lower
  have heNumeric : (2055009535397/1000000000000 : ℝ)/4 ≤ Real.exp (-1332027746173/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055009535397/1000000000000 : ℝ)/4 ≤ Real.exp ((993/8192 : ℝ)-(787229693399/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (993/8192 : ℝ) (1987/16384 : ℝ) (787229693399/1000000000000 : ℝ) (2055009535397/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0077; no trusted numerical premise.
theorem cover8_leaf0077_exp_radius : (62381618221921659/62500000000000000 : ℝ) ≤ Real.exp ((-497/32768 : ℝ)/8) ∧ Real.exp ((-497/32768 : ℝ)/8) ≤ (199621178310149309/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-497/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0077_exp_lower : (460059622299020961/500000000000000000 : ℝ) ≤ Real.exp ((-2664064116629/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664064116629/4000000000000 : ℝ)/8) ≤ (920119244598041923/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664064116629/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0077_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128437819041/62500000000 : ℝ) ≤ 4*Real.exp (1987/16384 : ℝ)*Real.exp (-mu (radius 8 (497/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (128437819041/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (497/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0077_exp_radius
  have hrNumeric : (492473603437/500000000000 : ℝ) ≤ Real.exp (-497/32768 : ℝ) ∧ Real.exp (-497/32768 : ℝ) ≤ (1575915531/1600000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492473603437/500000000000 : ℝ) ≤ (radius 8 (497/4096 : ℝ)) ∧ (radius 8 (497/4096 : ℝ)) ≤ (1575915531/1600000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (497/4096 : ℝ)) (492473603437/500000000000 : ℝ) (1575915531/1600000000 : ℝ) (172855429967/1000000000000 : ℝ) (172855429973/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (497/4096 : ℝ)) (492473603437/500000000000 : ℝ) (1575915531/1600000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (497/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492473603437/500000000000 : ℝ) (1575915531/1600000000 : ℝ) (992473603437/1000000000000 : ℝ) (496236801719/500000000000 : ℝ) (496222532457/500000000000 : ℝ) (248111266229/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (497/4096 : ℝ)) 1 (992473603437/1000000000000 : ℝ) (496236801719/500000000000 : ℝ) (496222532457/500000000000 : ℝ) (248111266229/250000000000 : ℝ) (39698373367/40000000000 : ℝ) (992459334177/1000000000000 : ℝ) (124057416759/125000000000 : ℝ) (39698373363/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (497/4096 : ℝ)) 2 (39698373367/40000000000 : ℝ) (992459334177/1000000000000 : ℝ) (124057416759/125000000000 : ℝ) (39698373363/40000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (497/4096 : ℝ)) 3 (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (497/4096 : ℝ)) 4 (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (497/4096 : ℝ)) 5 (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (497/4096 : ℝ)) 6 (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (497/4096 : ℝ)) 7 (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (497/4096 : ℝ))) (172855429967/1000000000000 : ℝ) (172855429973/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (497/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (172855429967/1000000000000 : ℝ) (172855429973/1000000000000 : ℝ) (586427714983/1000000000000 : ℝ) (586427714987/1000000000000 : ℝ) (207879430179/500000000000 : ℝ) (415758860367/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (497/4096 : ℝ))) 1 (586427714983/1000000000000 : ℝ) (586427714987/1000000000000 : ℝ) (207879430179/500000000000 : ℝ) (415758860367/1000000000000 : ℝ) (50109328767/100000000000 : ℝ) (501093287677/1000000000000 : ℝ) (493773752303/1000000000000 : ℝ) (493773752311/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (497/4096 : ℝ))) 2 (50109328767/100000000000 : ℝ) (501093287677/1000000000000 : ℝ) (493773752303/1000000000000 : ℝ) (493773752311/1000000000000 : ℝ) (248716759993/500000000000 : ℝ) (248716759997/500000000000 : ℝ) (497420056799/1000000000000 : ℝ) (62177507101/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (497/4096 : ℝ))) 3 (248716759993/500000000000 : ℝ) (248716759997/500000000000 : ℝ) (497420056799/1000000000000 : ℝ) (62177507101/125000000000 : ℝ) (62178348549/125000000000 : ℝ) (497426788401/1000000000000 : ℝ) (248713394173/500000000000 : ℝ) (124356697089/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (497/4096 : ℝ))) 4 (62178348549/125000000000 : ℝ) (497426788401/1000000000000 : ℝ) (248713394173/500000000000 : ℝ) (124356697089/250000000000 : ℝ) (497426788369/1000000000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (497/4096 : ℝ))) 5 (497426788369/1000000000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (497/4096 : ℝ))) 6 (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (497/4096 : ℝ))) 7 (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (497/4096 : ℝ)) hmem 8 (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (497/4096 : ℝ))) hcmem 8 (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (497/4096 : ℝ)) (992459334123/1000000000000 : ℝ) (496229667063/500000000000 : ℝ) (31089174273/62500000000 : ℝ) (497426788379/1000000000000 : ℝ) (157458576921/200000000000 : ℝ) (393646442313/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0077_exp_lower
  have heNumeric : (128437819041/62500000000 : ℝ)/4 ≤ Real.exp (-2664064116629/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128437819041/62500000000 : ℝ)/4 ≤ Real.exp ((1987/16384 : ℝ)-(393646442313/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1987/16384 : ℝ) (497/4096 : ℝ) (393646442313/500000000000 : ℝ) (128437819041/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0078; no trusted numerical premise.
theorem cover8_leaf0078_exp_radius : (249526234920811651/250000000000000000 : ℝ) ≤ Real.exp ((-1989/131072 : ℝ)/8) ∧ Real.exp ((-1989/131072 : ℝ)/8) ≤ (199620987936649321/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1989/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0078_exp_lower : (460059499553879319/500000000000000000 : ℝ) ≤ Real.exp ((-666018163579/1000000000000 : ℝ)/8) ∧ Real.exp ((-666018163579/1000000000000 : ℝ)/8) ≤ (920118999107758639/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666018163579/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0078_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055000718413/1000000000000 : ℝ) ≤ 4*Real.exp (497/4096 : ℝ)*Real.exp (-mu (radius 8 (1989/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2055000718413/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1989/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0078_exp_radius
  have hrNumeric : (15389682693/15625000000 : ℝ) ≤ Real.exp (-1989/131072 : ℝ) ∧ Real.exp (-1989/131072 : ℝ) ≤ (984939692353/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15389682693/15625000000 : ℝ) ≤ (radius 8 (1989/16384 : ℝ)) ∧ (radius 8 (1989/16384 : ℝ)) ≤ (984939692353/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1989/16384 : ℝ)) (15389682693/15625000000 : ℝ) (984939692353/1000000000000 : ℝ) (34579648597/200000000000 : ℝ) (10806140187/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1989/16384 : ℝ)) (15389682693/15625000000 : ℝ) (984939692353/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1989/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15389682693/15625000000 : ℝ) (984939692353/1000000000000 : ℝ) (31014682693/31250000000 : ℝ) (992469846177/1000000000000 : ℝ) (248110319761/250000000000 : ℝ) (496220639523/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1989/16384 : ℝ)) 1 (31014682693/31250000000 : ℝ) (992469846177/1000000000000 : ℝ) (248110319761/250000000000 : ℝ) (496220639523/500000000000 : ℝ) (99245556261/100000000000 : ℝ) (248113890653/250000000000 : ℝ) (992455562507/1000000000000 : ℝ) (992455562509/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1989/16384 : ℝ)) 2 (99245556261/100000000000 : ℝ) (248113890653/250000000000 : ℝ) (992455562507/1000000000000 : ℝ) (992455562509/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1989/16384 : ℝ)) 3 (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1989/16384 : ℝ)) 4 (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1989/16384 : ℝ)) 5 (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1989/16384 : ℝ)) 6 (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1989/16384 : ℝ)) 7 (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1989/16384 : ℝ))) (34579648597/200000000000 : ℝ) (10806140187/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1989/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (34579648597/200000000000 : ℝ) (10806140187/62500000000 : ℝ) (146612280373/250000000000 : ℝ) (73306140187/125000000000 : ℝ) (415810344971/1000000000000 : ℝ) (20790517249/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1989/16384 : ℝ))) 1 (146612280373/250000000000 : ℝ) (73306140187/125000000000 : ℝ) (415810344971/1000000000000 : ℝ) (20790517249/50000000000 : ℝ) (501129733231/1000000000000 : ℝ) (250564866619/500000000000 : ℝ) (61726667089/125000000000 : ℝ) (6172666709/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1989/16384 : ℝ))) 2 (501129733231/1000000000000 : ℝ) (250564866619/500000000000 : ℝ) (61726667089/125000000000 : ℝ) (6172666709/12500000000 : ℝ) (497471534971/1000000000000 : ℝ) (497471534979/1000000000000 : ℝ) (497458084357/1000000000000 : ℝ) (99491616873/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1989/16384 : ℝ))) 3 (497471534971/1000000000000 : ℝ) (497471534979/1000000000000 : ℝ) (497458084357/1000000000000 : ℝ) (99491616873/200000000000 : ℝ) (7772887651/15625000000 : ℝ) (62183101209/125000000000 : ℝ) (248732404809/500000000000 : ℝ) (497464809627/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1989/16384 : ℝ))) 4 (7772887651/15625000000 : ℝ) (62183101209/125000000000 : ℝ) (248732404809/500000000000 : ℝ) (497464809627/1000000000000 : ℝ) (497464809641/1000000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1989/16384 : ℝ))) 5 (497464809641/1000000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1989/16384 : ℝ))) 6 (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1989/16384 : ℝ))) 7 (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1989/16384 : ℝ)) hmem 8 (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1989/16384 : ℝ))) hcmem 8 (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1989/16384 : ℝ)) (496227781279/500000000000 : ℝ) (992455562561/1000000000000 : ℝ) (12436620241/25000000000 : ℝ) (9949296193/20000000000 : ℝ) (157471210837/200000000000 : ℝ) (196839013551/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0078_exp_lower
  have heNumeric : (2055000718413/1000000000000 : ℝ)/4 ≤ Real.exp (-666018163579/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055000718413/1000000000000 : ℝ)/4 ≤ Real.exp ((497/4096 : ℝ)-(196839013551/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (497/4096 : ℝ) (1989/16384 : ℝ) (196839013551/250000000000 : ℝ) (2055000718413/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0079; no trusted numerical premise.
theorem cover8_leaf0079_exp_radius : (199620797563330887/200000000000000000 : ℝ) ≤ Real.exp ((-995/65536 : ℝ)/8) ∧ Real.exp ((-995/65536 : ℝ)/8) ≤ (249525996954163609/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-995/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0079_exp_lower : (115014844512948339/125000000000000000 : ℝ) ≤ Real.exp ((-2664081105543/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664081105543/4000000000000 : ℝ)/8) ≤ (920118756103586713/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664081105543/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0079_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027498188299/500000000000 : ℝ) ≤ 4*Real.exp (1989/16384 : ℝ)*Real.exp (-mu (radius 8 (995/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027498188299/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (995/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0079_exp_radius
  have hrNumeric : (984932177887/1000000000000 : ℝ) ≤ Real.exp (-995/65536 : ℝ) ∧ Real.exp (-995/65536 : ℝ) ≤ (30779130559/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984932177887/1000000000000 : ℝ) ≤ (radius 8 (995/8192 : ℝ)) ∧ (radius 8 (995/8192 : ℝ)) ≤ (30779130559/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (995/8192 : ℝ)) (984932177887/1000000000000 : ℝ) (30779130559/31250000000 : ℝ) (86470522377/500000000000 : ℝ) (172941044761/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (995/8192 : ℝ)) (984932177887/1000000000000 : ℝ) (30779130559/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (995/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984932177887/1000000000000 : ℝ) (30779130559/31250000000 : ℝ) (992466088943/1000000000000 : ℝ) (62029130559/62500000000 : ℝ) (248109373297/250000000000 : ℝ) (99243749319/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (995/8192 : ℝ)) 1 (992466088943/1000000000000 : ℝ) (62029130559/62500000000 : ℝ) (248109373297/250000000000 : ℝ) (99243749319/100000000000 : ℝ) (198490358213/200000000000 : ℝ) (992451791067/1000000000000 : ℝ) (496225895481/500000000000 : ℝ) (198490358193/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (995/8192 : ℝ)) 2 (198490358213/200000000000 : ℝ) (992451791067/1000000000000 : ℝ) (496225895481/500000000000 : ℝ) (198490358193/200000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (995/8192 : ℝ)) 3 (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (995/8192 : ℝ)) 4 (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (995/8192 : ℝ)) 5 (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (995/8192 : ℝ)) 6 (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (995/8192 : ℝ)) 7 (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (995/8192 : ℝ))) (86470522377/500000000000 : ℝ) (172941044761/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (995/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (86470522377/500000000000 : ℝ) (172941044761/1000000000000 : ℝ) (586470522377/1000000000000 : ℝ) (586470522381/1000000000000 : ℝ) (103965452421/250000000000 : ℝ) (415861809693/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (995/8192 : ℝ))) 1 (586470522377/1000000000000 : ℝ) (586470522381/1000000000000 : ℝ) (103965452421/250000000000 : ℝ) (415861809693/1000000000000 : ℝ) (50116616603/100000000000 : ℝ) (501166166037/1000000000000 : ℝ) (493852905997/1000000000000 : ℝ) (98770581201/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (995/8192 : ℝ))) 2 (50116616603/100000000000 : ℝ) (501166166037/1000000000000 : ℝ) (493852905997/1000000000000 : ℝ) (98770581201/200000000000 : ℝ) (497509536013/1000000000000 : ℝ) (497509536021/1000000000000 : ℝ) (99499219591/200000000000 : ℝ) (124374024491/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (995/8192 : ℝ))) 3 (497509536013/1000000000000 : ℝ) (497509536021/1000000000000 : ℝ) (99499219591/200000000000 : ℝ) (124374024491/250000000000 : ℝ) (62187852123/125000000000 : ℝ) (497502816993/1000000000000 : ℝ) (248751408469/500000000000 : ℝ) (124375704237/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (995/8192 : ℝ))) 4 (62187852123/125000000000 : ℝ) (497502816993/1000000000000 : ℝ) (248751408469/500000000000 : ℝ) (124375704237/250000000000 : ℝ) (497502816961/1000000000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (995/8192 : ℝ))) 5 (497502816961/1000000000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (995/8192 : ℝ))) 6 (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (995/8192 : ℝ))) 7 (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (995/8192 : ℝ)) hmem 8 (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (995/8192 : ℝ))) hcmem 8 (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (995/8192 : ℝ)) (992451791013/1000000000000 : ℝ) (124056473877/125000000000 : ℝ) (1554696303/3125000000 : ℝ) (497502816971/1000000000000 : ℝ) (393709601073/500000000000 : ℝ) (787419202167/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0079_exp_lower
  have heNumeric : (1027498188299/500000000000 : ℝ)/4 ≤ Real.exp (-2664081105543/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027498188299/500000000000 : ℝ)/4 ≤ Real.exp ((1989/16384 : ℝ)-(787419202167/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1989/16384 : ℝ) (995/8192 : ℝ) (787419202167/1000000000000 : ℝ) (1027498188299/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0080; no trusted numerical premise.
theorem cover8_leaf0080_exp_radius : (998103035950970037/1000000000000000000 : ℝ) ≤ Real.exp ((-1991/131072 : ℝ)/8) ∧ Real.exp ((-1991/131072 : ℝ)/8) ≤ (499051517975485019/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1991/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0080_exp_lower : (184023703117058829/200000000000000000 : ℝ) ≤ Real.exp ((-1332044735159/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332044735159/2000000000000 : ℝ)/8) ≤ (460059257792647073/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332044735159/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0080_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054992079207/1000000000000 : ℝ) ≤ 4*Real.exp (995/8192 : ℝ)*Real.exp (-mu (radius 8 (1991/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054992079207/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1991/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0080_exp_radius
  have hrNumeric : (24623116587/25000000000 : ℝ) ≤ Real.exp (-1991/131072 : ℝ) ∧ Real.exp (-1991/131072 : ℝ) ≤ (984924663481/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24623116587/25000000000 : ℝ) ≤ (radius 8 (1991/16384 : ℝ)) ∧ (radius 8 (1991/16384 : ℝ)) ≤ (984924663481/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1991/16384 : ℝ)) (24623116587/25000000000 : ℝ) (984924663481/1000000000000 : ℝ) (43245958819/250000000000 : ℝ) (86491917641/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1991/16384 : ℝ)) (24623116587/25000000000 : ℝ) (984924663481/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1991/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24623116587/25000000000 : ℝ) (984924663481/1000000000000 : ℝ) (49623116587/50000000000 : ℝ) (992462331741/1000000000000 : ℝ) (992433707347/1000000000000 : ℝ) (992433707349/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1991/16384 : ℝ)) 1 (49623116587/50000000000 : ℝ) (992462331741/1000000000000 : ℝ) (992433707347/1000000000000 : ℝ) (992433707349/1000000000000 : ℝ) (992448019543/1000000000000 : ℝ) (198489603909/200000000000 : ℝ) (12405600243/12500000000 : ℝ) (496224009721/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1991/16384 : ℝ)) 2 (992448019543/1000000000000 : ℝ) (198489603909/200000000000 : ℝ) (12405600243/12500000000 : ℝ) (496224009721/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1991/16384 : ℝ)) 3 (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1991/16384 : ℝ)) 4 (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1991/16384 : ℝ)) 5 (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1991/16384 : ℝ)) 6 (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1991/16384 : ℝ)) 7 (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1991/16384 : ℝ))) (43245958819/250000000000 : ℝ) (86491917641/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1991/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43245958819/250000000000 : ℝ) (86491917641/500000000000 : ℝ) (293245958819/500000000000 : ℝ) (586491917641/1000000000000 : ℝ) (103978313627/250000000000 : ℝ) (103978313629/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1991/16384 : ℝ))) 1 (293245958819/500000000000 : ℝ) (586491917641/1000000000000 : ℝ) (103978313627/250000000000 : ℝ) (103978313629/250000000000 : ℝ) (501202586073/1000000000000 : ℝ) (501202586079/1000000000000 : ℝ) (123473115041/250000000000 : ℝ) (493892460171/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1991/16384 : ℝ))) 2 (501202586073/1000000000000 : ℝ) (501202586079/1000000000000 : ℝ) (123473115041/250000000000 : ℝ) (493892460171/1000000000000 : ℝ) (248773761559/500000000000 : ℝ) (796076037/1600000000 : ℝ) (497534097601/1000000000000 : ℝ) (497534097609/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1991/16384 : ℝ))) 3 (248773761559/500000000000 : ℝ) (796076037/1600000000 : ℝ) (497534097601/1000000000000 : ℝ) (497534097609/1000000000000 : ℝ) (497540810359/1000000000000 : ℝ) (497540810367/1000000000000 : ℝ) (248770405157/500000000000 : ℝ) (248770405161/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1991/16384 : ℝ))) 4 (497540810359/1000000000000 : ℝ) (497540810367/1000000000000 : ℝ) (248770405157/500000000000 : ℝ) (248770405161/500000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1991/16384 : ℝ))) 5 (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1991/16384 : ℝ))) 6 (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1991/16384 : ℝ))) 7 (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1991/16384 : ℝ)) hmem 8 (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1991/16384 : ℝ))) hcmem 8 (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1991/16384 : ℝ)) (992448019491/1000000000000 : ℝ) (496224009747/500000000000 : ℝ) (15548150323/31250000000 : ℝ) (99508162069/200000000000 : ℝ) (787482328499/1000000000000 : ℝ) (787482328517/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0080_exp_lower
  have heNumeric : (2054992079207/1000000000000 : ℝ)/4 ≤ Real.exp (-1332044735159/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054992079207/1000000000000 : ℝ)/4 ≤ Real.exp ((995/8192 : ℝ)-(787482328517/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (995/8192 : ℝ) (1991/16384 : ℝ) (787482328517/1000000000000 : ℝ) (2054992079207/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0081; no trusted numerical premise.
theorem cover8_leaf0081_exp_radius : (3898836265961693/3906250000000000 : ℝ) ≤ Real.exp ((-249/16384 : ℝ)/8) ∧ Real.exp ((-249/16384 : ℝ)/8) ≤ (998102084086193409/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-249/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0081_exp_lower : (920118277548048367/1000000000000000000 : ℝ) ≤ Real.exp ((-2664097748809/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664097748809/4000000000000 : ℝ)/8) ≤ (57507392346753023/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664097748809/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0081_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054987826153/1000000000000 : ℝ) ≤ 4*Real.exp (1991/16384 : ℝ)*Real.exp (-mu (radius 8 (249/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2054987826153/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (249/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0081_exp_radius
  have hrNumeric : (984917149129/1000000000000 : ℝ) ≤ Real.exp (-249/16384 : ℝ) ∧ Real.exp (-249/16384 : ℝ) ≤ (98491714913/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984917149129/1000000000000 : ℝ) ≤ (radius 8 (249/2048 : ℝ)) ∧ (radius 8 (249/2048 : ℝ)) ≤ (98491714913/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (249/2048 : ℝ)) (984917149129/1000000000000 : ℝ) (98491714913/100000000000 : ℝ) (17302661457/100000000000 : ℝ) (10814163411/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (249/2048 : ℝ)) (984917149129/1000000000000 : ℝ) (98491714913/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (249/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984917149129/1000000000000 : ℝ) (98491714913/100000000000 : ℝ) (248114643641/250000000000 : ℝ) (198491714913/200000000000 : ℝ) (12405374019/12500000000 : ℝ) (992429921521/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (249/2048 : ℝ)) 1 (248114643641/250000000000 : ℝ) (198491714913/200000000000 : ℝ) (12405374019/12500000000 : ℝ) (992429921521/1000000000000 : ℝ) (496222124021/500000000000 : ℝ) (992444248043/1000000000000 : ℝ) (496222123969/500000000000 : ℝ) (49622212397/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (249/2048 : ℝ)) 2 (496222124021/500000000000 : ℝ) (992444248043/1000000000000 : ℝ) (496222123969/500000000000 : ℝ) (49622212397/50000000000 : ℝ) (99244424799/100000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (249/2048 : ℝ)) 3 (99244424799/100000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (249/2048 : ℝ)) 4 (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (249/2048 : ℝ)) 5 (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (249/2048 : ℝ)) 6 (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (249/2048 : ℝ)) 7 (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (249/2048 : ℝ))) (17302661457/100000000000 : ℝ) (10814163411/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (249/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17302661457/100000000000 : ℝ) (10814163411/62500000000 : ℝ) (117302661457/200000000000 : ℝ) (73314163411/125000000000 : ℝ) (207982339737/500000000000 : ℝ) (207982339741/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (249/2048 : ℝ))) 1 (117302661457/200000000000 : ℝ) (73314163411/125000000000 : ℝ) (207982339737/500000000000 : ℝ) (207982339741/500000000000 : ℝ) (501238993379/1000000000000 : ℝ) (100247798677/200000000000 : ℝ) (246965999619/500000000000 : ℝ) (98786399849/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (249/2048 : ℝ))) 2 (501238993379/1000000000000 : ℝ) (100247798677/200000000000 : ℝ) (246965999619/500000000000 : ℝ) (98786399849/200000000000 : ℝ) (124396374077/250000000000 : ℝ) (99517099263/200000000000 : ℝ) (124393020829/250000000000 : ℝ) (497572083323/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (249/2048 : ℝ))) 3 (124396374077/250000000000 : ℝ) (99517099263/200000000000 : ℝ) (124393020829/250000000000 : ℝ) (497572083323/1000000000000 : ℝ) (124394697453/250000000000 : ℝ) (497578789819/1000000000000 : ℝ) (248789394883/500000000000 : ℝ) (248789394887/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (249/2048 : ℝ))) 4 (124394697453/250000000000 : ℝ) (497578789819/1000000000000 : ℝ) (248789394883/500000000000 : ℝ) (248789394887/500000000000 : ℝ) (497578789789/1000000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (249/2048 : ℝ))) 5 (497578789789/1000000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (249/2048 : ℝ))) 6 (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (249/2048 : ℝ))) 7 (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (249/2048 : ℝ)) hmem 8 (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (249/2048 : ℝ))) hcmem 8 (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (249/2048 : ℝ)) (992444247989/1000000000000 : ℝ) (124055530999/125000000000 : ℝ) (124394697447/250000000000 : ℝ) (497578789797/1000000000000 : ℝ) (393772716639/500000000000 : ℝ) (49221589581/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0081_exp_lower
  have heNumeric : (2054987826153/1000000000000 : ℝ)/4 ≤ Real.exp (-2664097748809/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054987826153/1000000000000 : ℝ)/4 ≤ Real.exp ((1991/16384 : ℝ)-(49221589581/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1991/16384 : ℝ) (249/2048 : ℝ) (49221589581/62500000000 : ℝ) (2054987826153/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0082; no trusted numerical premise.
theorem cover8_leaf0082_exp_radius : (249525283055581137/250000000000000000 : ℝ) ≤ Real.exp ((-1993/131072 : ℝ)/8) ∧ Real.exp ((-1993/131072 : ℝ)/8) ≤ (998101132222324549/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1993/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0082_exp_lower : (920118041991502407/1000000000000000000 : ℝ) ≤ Real.exp ((-666026485257/1000000000000 : ℝ)/8) ∧ Real.exp ((-666026485257/1000000000000 : ℝ)/8) ≤ (115014755248937801/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666026485257/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0082_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054983617429/1000000000000 : ℝ) ≤ 4*Real.exp (249/2048 : ℝ)*Real.exp (-mu (radius 8 (1993/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054983617429/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1993/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0082_exp_radius
  have hrNumeric : (246227408709/250000000000 : ℝ) ≤ Real.exp (-1993/131072 : ℝ) ∧ Real.exp (-1993/131072 : ℝ) ≤ (984909634837/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246227408709/250000000000 : ℝ) ≤ (radius 8 (1993/16384 : ℝ)) ∧ (radius 8 (1993/16384 : ℝ)) ≤ (984909634837/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1993/16384 : ℝ)) (246227408709/250000000000 : ℝ) (984909634837/1000000000000 : ℝ) (173069382633/1000000000000 : ℝ) (2163367283/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1993/16384 : ℝ)) (246227408709/250000000000 : ℝ) (984909634837/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1993/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246227408709/250000000000 : ℝ) (984909634837/1000000000000 : ℝ) (496227408709/500000000000 : ℝ) (992454817419/1000000000000 : ℝ) (992426135707/1000000000000 : ℝ) (992426135709/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1993/16384 : ℝ)) 1 (496227408709/500000000000 : ℝ) (992454817419/1000000000000 : ℝ) (992426135707/1000000000000 : ℝ) (992426135709/1000000000000 : ℝ) (496220238281/500000000000 : ℝ) (248110119141/250000000000 : ℝ) (496220238229/500000000000 : ℝ) (992440476461/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1993/16384 : ℝ)) 2 (496220238281/500000000000 : ℝ) (248110119141/250000000000 : ℝ) (496220238229/500000000000 : ℝ) (992440476461/1000000000000 : ℝ) (99244047651/100000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1993/16384 : ℝ)) 3 (99244047651/100000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1993/16384 : ℝ)) 4 (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1993/16384 : ℝ)) 5 (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1993/16384 : ℝ)) 6 (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1993/16384 : ℝ)) 7 (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1993/16384 : ℝ))) (173069382633/1000000000000 : ℝ) (2163367283/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1993/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (173069382633/1000000000000 : ℝ) (2163367283/12500000000 : ℝ) (146633672829/250000000000 : ℝ) (14663367283/25000000000 : ℝ) (52002010573/125000000000 : ℝ) (416016084593/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1993/16384 : ℝ))) 1 (146633672829/250000000000 : ℝ) (14663367283/25000000000 : ℝ) (52002010573/125000000000 : ℝ) (416016084593/1000000000000 : ℝ) (10025507759/20000000000 : ℝ) (501275387957/1000000000000 : ℝ) (493971523221/1000000000000 : ℝ) (493971523229/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1993/16384 : ℝ))) 2 (10025507759/20000000000 : ℝ) (501275387957/1000000000000 : ℝ) (493971523221/1000000000000 : ℝ) (493971523229/1000000000000 : ℝ) (99524691117/200000000000 : ℝ) (497623455593/1000000000000 : ℝ) (248805027551/500000000000 : ℝ) (49761005511/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1993/16384 : ℝ))) 3 (99524691117/200000000000 : ℝ) (497623455593/1000000000000 : ℝ) (248805027551/500000000000 : ℝ) (49761005511/100000000000 : ℝ) (497616755343/1000000000000 : ℝ) (62202094419/125000000000 : ℝ) (248808377649/500000000000 : ℝ) (497616755307/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1993/16384 : ℝ))) 4 (497616755343/1000000000000 : ℝ) (62202094419/125000000000 : ℝ) (248808377649/500000000000 : ℝ) (497616755307/1000000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1993/16384 : ℝ))) 5 (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1993/16384 : ℝ))) 6 (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1993/16384 : ℝ))) 7 (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1993/16384 : ℝ)) hmem 8 (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1993/16384 : ℝ))) hcmem 8 (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1993/16384 : ℝ)) (992440476509/1000000000000 : ℝ) (992440476513/1000000000000 : ℝ) (12440418883/25000000000 : ℝ) (49761675533/100000000000 : ℝ) (787608516487/1000000000000 : ℝ) (787608516507/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0082_exp_lower
  have heNumeric : (2054983617429/1000000000000 : ℝ)/4 ≤ Real.exp (-666026485257/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054983617429/1000000000000 : ℝ)/4 ≤ Real.exp ((249/2048 : ℝ)-(787608516507/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (249/2048 : ℝ) (1993/16384 : ℝ) (787608516507/1000000000000 : ℝ) (2054983617429/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0083; no trusted numerical premise.
theorem cover8_leaf0083_exp_radius : (199620036071872691/200000000000000000 : ℝ) ≤ Real.exp ((-997/65536 : ℝ)/8) ∧ Real.exp ((-997/65536 : ℝ)/8) ≤ (7797657659057527/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-997/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0083_exp_lower : (184023561782808831/200000000000000000 : ℝ) ≤ Real.exp ((-2664114047031/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664114047031/4000000000000 : ℝ)/8) ≤ (230029452228511039/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664114047031/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0083_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128436215813/62500000000 : ℝ) ≤ 4*Real.exp (1993/16384 : ℝ)*Real.exp (-mu (radius 8 (997/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (128436215813/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (997/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0083_exp_radius
  have hrNumeric : (984902120601/1000000000000 : ℝ) ≤ Real.exp (-997/65536 : ℝ) ∧ Real.exp (-997/65536 : ℝ) ≤ (492451060301/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984902120601/1000000000000 : ℝ) ≤ (radius 8 (997/8192 : ℝ)) ∧ (radius 8 (997/8192 : ℝ)) ≤ (492451060301/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (997/8192 : ℝ)) (984902120601/1000000000000 : ℝ) (492451060301/500000000000 : ℝ) (6924485579/40000000000 : ℝ) (173112139481/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (997/8192 : ℝ)) (984902120601/1000000000000 : ℝ) (492451060301/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (997/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984902120601/1000000000000 : ℝ) (492451060301/500000000000 : ℝ) (9924510603/10000000000 : ℝ) (992451060301/1000000000000 : ℝ) (99242234991/100000000000 : ℝ) (992422349911/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (997/8192 : ℝ)) 1 (9924510603/10000000000 : ℝ) (992451060301/1000000000000 : ℝ) (99242234991/100000000000 : ℝ) (992422349911/1000000000000 : ℝ) (198487341021/200000000000 : ℝ) (496218352553/500000000000 : ℝ) (992436705001/1000000000000 : ℝ) (992436705003/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (997/8192 : ℝ)) 2 (198487341021/200000000000 : ℝ) (496218352553/500000000000 : ℝ) (992436705001/1000000000000 : ℝ) (992436705003/1000000000000 : ℝ) (992436705053/1000000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (997/8192 : ℝ)) 3 (992436705053/1000000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (997/8192 : ℝ)) 4 (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (997/8192 : ℝ)) 5 (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (997/8192 : ℝ)) 6 (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (997/8192 : ℝ)) 7 (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (997/8192 : ℝ))) (6924485579/40000000000 : ℝ) (173112139481/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (997/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (6924485579/40000000000 : ℝ) (173112139481/1000000000000 : ℝ) (586556069737/1000000000000 : ℝ) (586556069741/1000000000000 : ℝ) (416067469859/1000000000000 : ℝ) (416067469867/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (997/8192 : ℝ))) 1 (586556069737/1000000000000 : ℝ) (586556069741/1000000000000 : ℝ) (416067469859/1000000000000 : ℝ) (416067469867/1000000000000 : ℝ) (250655884899/500000000000 : ℝ) (125327942451/250000000000 : ℝ) (494011032129/1000000000000 : ℝ) (494011032137/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (997/8192 : ℝ))) 2 (250655884899/500000000000 : ℝ) (125327942451/250000000000 : ℝ) (494011032129/1000000000000 : ℝ) (494011032137/1000000000000 : ℝ) (497661400963/1000000000000 : ℝ) (497661400971/1000000000000 : ℝ) (497648012973/1000000000000 : ℝ) (497648012981/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (997/8192 : ℝ))) 3 (497661400963/1000000000000 : ℝ) (497661400971/1000000000000 : ℝ) (497648012973/1000000000000 : ℝ) (497648012981/1000000000000 : ℝ) (62206838371/125000000000 : ℝ) (15551709593/31250000000 : ℝ) (248827353461/500000000000 : ℝ) (497654706931/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (997/8192 : ℝ))) 4 (62206838371/125000000000 : ℝ) (15551709593/31250000000 : ℝ) (248827353461/500000000000 : ℝ) (497654706931/1000000000000 : ℝ) (99530941389/200000000000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (997/8192 : ℝ))) 5 (99530941389/200000000000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (997/8192 : ℝ))) 6 (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (997/8192 : ℝ))) 7 (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (997/8192 : ℝ)) hmem 8 (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (997/8192 : ℝ))) hcmem 8 (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (997/8192 : ℝ)) (248109176263/250000000000 : ℝ) (198487341011/200000000000 : ℝ) (1943963699/3906250000 : ℝ) (248827353477/500000000000 : ℝ) (157534315629/200000000000 : ℝ) (196917894541/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0083_exp_lower
  have heNumeric : (128436215813/62500000000 : ℝ)/4 ≤ Real.exp (-2664114047031/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128436215813/62500000000 : ℝ)/4 ≤ Real.exp ((1993/16384 : ℝ)-(196917894541/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1993/16384 : ℝ) (997/8192 : ℝ) (196917894541/250000000000 : ℝ) (128436215813/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0084; no trusted numerical premise.
theorem cover8_leaf0084_exp_radius : (998099228497310129/1000000000000000000 : ℝ) ≤ Real.exp ((-1995/131072 : ℝ)/8) ∧ Real.exp ((-1995/131072 : ℝ)/8) ≤ (99809922849731013/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1995/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0084_exp_lower : (920117578311876241/1000000000000000000 : ℝ) ≤ Real.exp ((-53282441339/80000000000 : ℝ)/8) ∧ Real.exp ((-53282441339/80000000000 : ℝ)/8) ≤ (460058789155938121/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-53282441339/80000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0084_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102748766641/50000000000 : ℝ) ≤ 4*Real.exp (997/8192 : ℝ)*Real.exp (-mu (radius 8 (1995/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (102748766641/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1995/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0084_exp_radius
  have hrNumeric : (984894606423/1000000000000 : ℝ) ≤ Real.exp (-1995/131072 : ℝ) ∧ Real.exp (-1995/131072 : ℝ) ≤ (123111825803/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984894606423/1000000000000 : ℝ) ≤ (radius 8 (1995/16384 : ℝ)) ∧ (radius 8 (1995/16384 : ℝ)) ≤ (123111825803/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1995/16384 : ℝ)) (984894606423/1000000000000 : ℝ) (123111825803/125000000000 : ℝ) (43288721277/250000000000 : ℝ) (34630977023/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1995/16384 : ℝ)) (984894606423/1000000000000 : ℝ) (123111825803/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1995/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984894606423/1000000000000 : ℝ) (123111825803/125000000000 : ℝ) (992447303211/1000000000000 : ℝ) (248111825803/250000000000 : ℝ) (496209282063/500000000000 : ℝ) (31013080129/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1995/16384 : ℝ)) 1 (992447303211/1000000000000 : ℝ) (248111825803/250000000000 : ℝ) (496209282063/500000000000 : ℝ) (31013080129/31250000000 : ℝ) (248108233417/250000000000 : ℝ) (99243293367/100000000000 : ℝ) (248108233391/250000000000 : ℝ) (496216466783/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1995/16384 : ℝ)) 2 (248108233417/250000000000 : ℝ) (99243293367/100000000000 : ℝ) (248108233391/250000000000 : ℝ) (496216466783/500000000000 : ℝ) (62027058351/62500000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1995/16384 : ℝ)) 3 (62027058351/62500000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1995/16384 : ℝ)) 4 (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1995/16384 : ℝ)) 5 (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1995/16384 : ℝ)) 6 (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1995/16384 : ℝ)) 7 (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1995/16384 : ℝ))) (43288721277/250000000000 : ℝ) (34630977023/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1995/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43288721277/250000000000 : ℝ) (34630977023/200000000000 : ℝ) (293288721277/500000000000 : ℝ) (293288721279/500000000000 : ℝ) (416118835319/1000000000000 : ℝ) (416118835329/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1995/16384 : ℝ))) 1 (293288721277/500000000000 : ℝ) (293288721279/500000000000 : ℝ) (416118835319/1000000000000 : ℝ) (416118835329/1000000000000 : ℝ) (62668517367/125000000000 : ℝ) (7833564671/15625000000 : ℝ) (247025262989/500000000000 : ℝ) (494050525987/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1995/16384 : ℝ))) 2 (62668517367/125000000000 : ℝ) (7833564671/15625000000 : ℝ) (247025262989/500000000000 : ℝ) (494050525987/1000000000000 : ℝ) (497699332457/1000000000000 : ℝ) (248849666233/500000000000 : ℝ) (31105372309/62500000000 : ℝ) (497685956953/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1995/16384 : ℝ))) 3 (497699332457/1000000000000 : ℝ) (248849666233/500000000000 : ℝ) (31105372309/62500000000 : ℝ) (497685956953/1000000000000 : ℝ) (4976926447/10000000000 : ℝ) (49769264471/100000000000 : ℝ) (99538528931/200000000000 : ℝ) (99538528933/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1995/16384 : ℝ))) 4 (4976926447/10000000000 : ℝ) (49769264471/100000000000 : ℝ) (99538528931/200000000000 : ℝ) (99538528933/200000000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1995/16384 : ℝ))) 5 (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1995/16384 : ℝ))) 6 (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1995/16384 : ℝ))) 7 (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1995/16384 : ℝ)) hmem 8 (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1995/16384 : ℝ))) hcmem 8 (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1995/16384 : ℝ)) (198486586723/200000000000 : ℝ) (496216466809/500000000000 : ℝ) (497692644677/1000000000000 : ℝ) (31105790293/62500000000 : ℝ) (787734618279/1000000000000 : ℝ) (7877346183/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0084_exp_lower
  have heNumeric : (102748766641/50000000000 : ℝ)/4 ≤ Real.exp (-53282441339/80000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102748766641/50000000000 : ℝ)/4 ≤ Real.exp ((997/8192 : ℝ)-(7877346183/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (997/8192 : ℝ) (1995/16384 : ℝ) (7877346183/10000000000 : ℝ) (102748766641/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0085; no trusted numerical premise.
theorem cover8_leaf0085_exp_radius : (998098276636164569/1000000000000000000 : ℝ) ≤ Real.exp ((-499/32768 : ℝ)/8) ∧ Real.exp ((-499/32768 : ℝ)/8) ≤ (99809827663616457/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-499/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0085_exp_lower : (920117350183731643/1000000000000000000 : ℝ) ≤ Real.exp ((-2664130000829/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664130000829/4000000000000 : ℝ)/8) ≤ (230029337545932911/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664130000829/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0085_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027485628421/500000000000 : ℝ) ≤ 4*Real.exp (1995/16384 : ℝ)*Real.exp (-mu (radius 8 (499/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027485628421/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (499/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0085_exp_radius
  have hrNumeric : (492443546151/500000000000 : ℝ) ≤ Real.exp (-499/32768 : ℝ) ∧ Real.exp (-499/32768 : ℝ) ≤ (984887092303/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492443546151/500000000000 : ℝ) ≤ (radius 8 (499/4096 : ℝ)) ∧ (radius 8 (499/4096 : ℝ)) ≤ (984887092303/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (499/4096 : ℝ)) (492443546151/500000000000 : ℝ) (984887092303/1000000000000 : ℝ) (173197619541/1000000000000 : ℝ) (43299404887/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (499/4096 : ℝ)) (492443546151/500000000000 : ℝ) (984887092303/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (499/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492443546151/500000000000 : ℝ) (984887092303/1000000000000 : ℝ) (992443546151/1000000000000 : ℝ) (124055443269/125000000000 : ℝ) (992414778357/1000000000000 : ℝ) (496207389179/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (499/4096 : ℝ)) 1 (992443546151/1000000000000 : ℝ) (124055443269/125000000000 : ℝ) (992414778357/1000000000000 : ℝ) (496207389179/500000000000 : ℝ) (496214581127/500000000000 : ℝ) (198485832451/200000000000 : ℝ) (992429162149/1000000000000 : ℝ) (992429162151/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (499/4096 : ℝ)) 2 (496214581127/500000000000 : ℝ) (198485832451/200000000000 : ℝ) (992429162149/1000000000000 : ℝ) (992429162151/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (499/4096 : ℝ)) 3 (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (499/4096 : ℝ)) 4 (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (499/4096 : ℝ)) 5 (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (499/4096 : ℝ)) 6 (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (499/4096 : ℝ)) 7 (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (499/4096 : ℝ))) (173197619541/1000000000000 : ℝ) (43299404887/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (499/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (173197619541/1000000000000 : ℝ) (43299404887/250000000000 : ℝ) (58659880977/100000000000 : ℝ) (293299404887/500000000000 : ℝ) (52021272623/125000000000 : ℝ) (208085090497/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (499/4096 : ℝ))) 1 (58659880977/100000000000 : ℝ) (293299404887/500000000000 : ℝ) (52021272623/125000000000 : ℝ) (208085090497/500000000000 : ℝ) (501384495377/1000000000000 : ℝ) (62673061923/125000000000 : ℝ) (494090004783/1000000000000 : ℝ) (61761250599/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (499/4096 : ℝ))) 2 (501384495377/1000000000000 : ℝ) (62673061923/125000000000 : ℝ) (494090004783/1000000000000 : ℝ) (61761250599/125000000000 : ℝ) (3110857813/6250000000 : ℝ) (62217156261/125000000000 : ℝ) (124430971757/250000000000 : ℝ) (497723887037/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (499/4096 : ℝ))) 3 (3110857813/6250000000 : ℝ) (62217156261/125000000000 : ℝ) (124430971757/250000000000 : ℝ) (497723887037/1000000000000 : ℝ) (248865284277/500000000000 : ℝ) (497730568563/1000000000000 : ℝ) (497730568509/1000000000000 : ℝ) (248865284259/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (499/4096 : ℝ))) 4 (248865284277/500000000000 : ℝ) (497730568563/1000000000000 : ℝ) (497730568509/1000000000000 : ℝ) (248865284259/500000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (499/4096 : ℝ))) 5 (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (499/4096 : ℝ))) 6 (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (499/4096 : ℝ))) 7 (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (499/4096 : ℝ)) hmem 8 (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (499/4096 : ℝ))) hcmem 8 (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (499/4096 : ℝ)) (992429162201/1000000000000 : ℝ) (992429162203/1000000000000 : ℝ) (497730568531/1000000000000 : ℝ) (497730568541/1000000000000 : ℝ) (787797636907/1000000000000 : ℝ) (393898818463/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0085_exp_lower
  have heNumeric : (1027485628421/500000000000 : ℝ)/4 ≤ Real.exp (-2664130000829/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027485628421/500000000000 : ℝ)/4 ≤ Real.exp ((1995/16384 : ℝ)-(393898818463/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1995/16384 : ℝ) (499/4096 : ℝ) (393898818463/500000000000 : ℝ) (1027485628421/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0086; no trusted numerical premise.
theorem cover8_leaf0086_exp_radius : (499048662387963387/500000000000000000 : ℝ) ≤ Real.exp ((-1997/131072 : ℝ)/8) ∧ Real.exp ((-1997/131072 : ℝ)/8) ≤ (39923892991037071/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1997/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0086_exp_lower : (920117124526618141/1000000000000000000 : ℝ) ≤ Real.exp ((-666034462193/1000000000000 : ℝ)/8) ∧ Real.exp ((-666034462193/1000000000000 : ℝ)/8) ≤ (460058562263309071/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666034462193/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0086_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027483612511/500000000000 : ℝ) ≤ 4*Real.exp (499/4096 : ℝ)*Real.exp (-mu (radius 8 (1997/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027483612511/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1997/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0086_exp_radius
  have hrNumeric : (492439789119/500000000000 : ℝ) ≤ Real.exp (-1997/131072 : ℝ) ∧ Real.exp (-1997/131072 : ℝ) ≤ (984879578239/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492439789119/500000000000 : ℝ) ≤ (radius 8 (1997/16384 : ℝ)) ∧ (radius 8 (1997/16384 : ℝ)) ≤ (984879578239/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1997/16384 : ℝ)) (492439789119/500000000000 : ℝ) (984879578239/1000000000000 : ℝ) (173240342783/1000000000000 : ℝ) (17324034279/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1997/16384 : ℝ)) (492439789119/500000000000 : ℝ) (984879578239/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1997/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492439789119/500000000000 : ℝ) (984879578239/1000000000000 : ℝ) (992439789119/1000000000000 : ℝ) (3101374341/3125000000 : ℝ) (496205496301/500000000000 : ℝ) (992410992603/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1997/16384 : ℝ)) 1 (992439789119/1000000000000 : ℝ) (3101374341/3125000000 : ℝ) (496205496301/500000000000 : ℝ) (992410992603/1000000000000 : ℝ) (49621269543/50000000000 : ℝ) (496212695431/500000000000 : ℝ) (248106347689/250000000000 : ℝ) (496212695379/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1997/16384 : ℝ)) 2 (49621269543/50000000000 : ℝ) (496212695431/500000000000 : ℝ) (248106347689/250000000000 : ℝ) (496212695379/500000000000 : ℝ) (124053173851/125000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1997/16384 : ℝ)) 3 (124053173851/125000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1997/16384 : ℝ)) 4 (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1997/16384 : ℝ)) 5 (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1997/16384 : ℝ)) 6 (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1997/16384 : ℝ)) 7 (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1997/16384 : ℝ))) (173240342783/1000000000000 : ℝ) (17324034279/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1997/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (173240342783/1000000000000 : ℝ) (17324034279/100000000000 : ℝ) (586620171391/1000000000000 : ℝ) (117324034279/200000000000 : ℝ) (52027688359/125000000000 : ℝ) (416221506881/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1997/16384 : ℝ))) 1 (586620171391/1000000000000 : ℝ) (117324034279/200000000000 : ℝ) (52027688359/125000000000 : ℝ) (416221506881/1000000000000 : ℝ) (501420839131/1000000000000 : ℝ) (250710419569/500000000000 : ℝ) (247064734279/500000000000 : ℝ) (247064734283/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1997/16384 : ℝ))) 2 (501420839131/1000000000000 : ℝ) (250710419569/500000000000 : ℝ) (247064734279/500000000000 : ℝ) (247064734283/500000000000 : ℝ) (124443788461/250000000000 : ℝ) (124443788463/250000000000 : ℝ) (248880901619/500000000000 : ℝ) (497761803247/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1997/16384 : ℝ))) 3 (124443788461/250000000000 : ℝ) (124443788463/250000000000 : ℝ) (248880901619/500000000000 : ℝ) (497761803247/1000000000000 : ℝ) (497768478541/1000000000000 : ℝ) (9955369571/20000000000 : ℝ) (15555264953/31250000000 : ℝ) (99553695701/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1997/16384 : ℝ))) 4 (497768478541/1000000000000 : ℝ) (9955369571/20000000000 : ℝ) (15555264953/31250000000 : ℝ) (99553695701/200000000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1997/16384 : ℝ))) 5 (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1997/16384 : ℝ))) 6 (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1997/16384 : ℝ))) 7 (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1997/16384 : ℝ)) hmem 8 (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1997/16384 : ℝ))) hcmem 8 (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1997/16384 : ℝ)) (992425390807/1000000000000 : ℝ) (99242539081/100000000000 : ℝ) (248884239259/500000000000 : ℝ) (7777632477/15625000000 : ℝ) (787860634049/1000000000000 : ℝ) (196965158517/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0086_exp_lower
  have heNumeric : (1027483612511/500000000000 : ℝ)/4 ≤ Real.exp (-666034462193/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027483612511/500000000000 : ℝ)/4 ≤ Real.exp ((499/4096 : ℝ)-(196965158517/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (499/4096 : ℝ) (1997/16384 : ℝ) (196965158517/250000000000 : ℝ) (1027483612511/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0087; no trusted numerical premise.
theorem cover8_leaf0087_exp_radius : (998096372916596743/1000000000000000000 : ℝ) ≤ Real.exp ((-999/65536 : ℝ)/8) ∧ Real.exp ((-999/65536 : ℝ)/8) ≤ (124762046614574593/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-999/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0087_exp_lower : (28753653166859337/31250000000000000 : ℝ) ≤ Real.exp ((-532829122163/800000000000 : ℝ)/8) ∧ Real.exp ((-532829122163/800000000000 : ℝ)/8) ≤ (184023380267899757/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532829122163/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0087_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102748161867/50000000000 : ℝ) ≤ 4*Real.exp (1997/16384 : ℝ)*Real.exp (-mu (radius 8 (999/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (102748161867/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (999/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0087_exp_radius
  have hrNumeric : (123109008029/125000000000 : ℝ) ≤ Real.exp (-999/65536 : ℝ) ∧ Real.exp (-999/65536 : ℝ) ≤ (984872064233/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123109008029/125000000000 : ℝ) ≤ (radius 8 (999/8192 : ℝ)) ∧ (radius 8 (999/8192 : ℝ)) ≤ (984872064233/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (999/8192 : ℝ)) (123109008029/125000000000 : ℝ) (984872064233/1000000000000 : ℝ) (43320763709/250000000000 : ℝ) (173283054843/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (999/8192 : ℝ)) (123109008029/125000000000 : ℝ) (984872064233/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (999/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123109008029/125000000000 : ℝ) (984872064233/1000000000000 : ℝ) (248109008029/250000000000 : ℝ) (992436032117/1000000000000 : ℝ) (496203603431/500000000000 : ℝ) (992407206863/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (999/8192 : ℝ)) 1 (248109008029/250000000000 : ℝ) (992436032117/1000000000000 : ℝ) (496203603431/500000000000 : ℝ) (992407206863/1000000000000 : ℝ) (992421619489/1000000000000 : ℝ) (99242161949/100000000000 : ℝ) (124052702423/125000000000 : ℝ) (496210809693/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (999/8192 : ℝ)) 2 (992421619489/1000000000000 : ℝ) (99242161949/100000000000 : ℝ) (124052702423/125000000000 : ℝ) (496210809693/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (999/8192 : ℝ)) 3 (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (999/8192 : ℝ)) 4 (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (999/8192 : ℝ)) 5 (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (999/8192 : ℝ)) 6 (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (999/8192 : ℝ)) 7 (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (999/8192 : ℝ))) (43320763709/250000000000 : ℝ) (173283054843/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (999/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43320763709/250000000000 : ℝ) (173283054843/1000000000000 : ℝ) (293320763709/500000000000 : ℝ) (293320763711/500000000000 : ℝ) (416272812991/1000000000000 : ℝ) (416272813001/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (999/8192 : ℝ))) 1 (293320763709/500000000000 : ℝ) (293320763711/500000000000 : ℝ) (416272812991/1000000000000 : ℝ) (416272813001/1000000000000 : ℝ) (125364292551/250000000000 : ℝ) (125364292553/250000000000 : ℝ) (49416891731/100000000000 : ℝ) (247084458659/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (999/8192 : ℝ))) 2 (125364292551/250000000000 : ℝ) (125364292553/250000000000 : ℝ) (49416891731/100000000000 : ℝ) (247084458659/500000000000 : ℝ) (497813043757/1000000000000 : ℝ) (99562608753/200000000000 : ℝ) (497799705581/1000000000000 : ℝ) (49779970559/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (999/8192 : ℝ))) 3 (497813043757/1000000000000 : ℝ) (99562608753/200000000000 : ℝ) (497799705581/1000000000000 : ℝ) (49779970559/100000000000 : ℝ) (497806374669/1000000000000 : ℝ) (248903187339/500000000000 : ℝ) (15556449207/31250000000 : ℝ) (497806374633/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (999/8192 : ℝ))) 4 (497806374669/1000000000000 : ℝ) (248903187339/500000000000 : ℝ) (15556449207/31250000000 : ℝ) (497806374633/1000000000000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (999/8192 : ℝ))) 5 (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (999/8192 : ℝ))) 6 (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (999/8192 : ℝ))) 7 (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (999/8192 : ℝ)) hmem 8 (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (999/8192 : ℝ))) hcmem 8 (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (999/8192 : ℝ)) (248105404859/250000000000 : ℝ) (496210809719/500000000000 : ℝ) (248903187323/500000000000 : ℝ) (1944556151/3906250000 : ℝ) (787923609717/1000000000000 : ℝ) (157584721947/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0087_exp_lower
  have heNumeric : (102748161867/50000000000 : ℝ)/4 ≤ Real.exp (-532829122163/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102748161867/50000000000 : ℝ)/4 ≤ Real.exp ((1997/16384 : ℝ)-(157584721947/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1997/16384 : ℝ) (999/8192 : ℝ) (157584721947/200000000000 : ℝ) (102748161867/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0088; no trusted numerical premise.
theorem cover8_leaf0088_exp_radius : (249523855264543619/250000000000000000 : ℝ) ≤ Real.exp ((-1999/131072 : ℝ)/8) ∧ Real.exp ((-1999/131072 : ℝ)/8) ≤ (998095421058174477/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1999/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0088_exp_lower : (230029170154845349/250000000000000000 : ℝ) ≤ Real.exp ((-1332076643531/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332076643531/2000000000000 : ℝ)/8) ≤ (920116680619381397/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332076643531/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0088_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027479646871/500000000000 : ℝ) ≤ 4*Real.exp (999/8192 : ℝ)*Real.exp (-mu (radius 8 (1999/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027479646871/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1999/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0088_exp_radius
  have hrNumeric : (984864550283/1000000000000 : ℝ) ≤ Real.exp (-1999/131072 : ℝ) ∧ Real.exp (-1999/131072 : ℝ) ≤ (246216137571/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984864550283/1000000000000 : ℝ) ≤ (radius 8 (1999/16384 : ℝ)) ∧ (radius 8 (1999/16384 : ℝ)) ≤ (246216137571/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1999/16384 : ℝ)) (984864550283/1000000000000 : ℝ) (246216137571/250000000000 : ℝ) (86662877857/500000000000 : ℝ) (4333143893/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1999/16384 : ℝ)) (984864550283/1000000000000 : ℝ) (246216137571/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1999/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984864550283/1000000000000 : ℝ) (246216137571/250000000000 : ℝ) (992432275141/1000000000000 : ℝ) (496216137571/500000000000 : ℝ) (62025213821/62500000000 : ℝ) (992403421137/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1999/16384 : ℝ)) 1 (992432275141/1000000000000 : ℝ) (496216137571/500000000000 : ℝ) (62025213821/62500000000 : ℝ) (992403421137/1000000000000 : ℝ) (496208924069/500000000000 : ℝ) (49620892407/50000000000 : ℝ) (992417848033/1000000000000 : ℝ) (198483569607/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1999/16384 : ℝ)) 2 (496208924069/500000000000 : ℝ) (49620892407/50000000000 : ℝ) (992417848033/1000000000000 : ℝ) (198483569607/200000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1999/16384 : ℝ)) 3 (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1999/16384 : ℝ)) 4 (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1999/16384 : ℝ)) 5 (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1999/16384 : ℝ)) 6 (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1999/16384 : ℝ)) 7 (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1999/16384 : ℝ))) (86662877857/500000000000 : ℝ) (4333143893/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1999/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (86662877857/500000000000 : ℝ) (4333143893/25000000000 : ℝ) (586662877857/1000000000000 : ℝ) (29333143893/50000000000 : ℝ) (416324099367/1000000000000 : ℝ) (666118559/1600000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1999/16384 : ℝ))) 1 (586662877857/1000000000000 : ℝ) (29333143893/50000000000 : ℝ) (416324099367/1000000000000 : ℝ) (666118559/1600000000 : ℝ) (125373372153/250000000000 : ℝ) (250746744309/500000000000 : ℝ) (247104175529/500000000000 : ℝ) (98841670213/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1999/16384 : ℝ))) 2 (125373372153/250000000000 : ℝ) (250746744309/500000000000 : ℝ) (247104175529/500000000000 : ℝ) (98841670213/200000000000 : ℝ) (99570183967/200000000000 : ℝ) (248925459921/500000000000 : ℝ) (497837594073/1000000000000 : ℝ) (497837594081/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1999/16384 : ℝ))) 3 (99570183967/200000000000 : ℝ) (248925459921/500000000000 : ℝ) (497837594073/1000000000000 : ℝ) (497837594081/1000000000000 : ℝ) (248922128477/500000000000 : ℝ) (248922128481/500000000000 : ℝ) (497844256909/1000000000000 : ℝ) (497844256917/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1999/16384 : ℝ))) 4 (248922128477/500000000000 : ℝ) (248922128481/500000000000 : ℝ) (497844256909/1000000000000 : ℝ) (497844256917/1000000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1999/16384 : ℝ))) 5 (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1999/16384 : ℝ))) 6 (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1999/16384 : ℝ))) 7 (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1999/16384 : ℝ)) hmem 8 (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1999/16384 : ℝ))) hcmem 8 (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1999/16384 : ℝ)) (198483569617/200000000000 : ℝ) (124052231011/125000000000 : ℝ) (497844256931/1000000000000 : ℝ) (24892212847/50000000000 : ℝ) (157597312787/200000000000 : ℝ) (787986563953/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0088_exp_lower
  have heNumeric : (1027479646871/500000000000 : ℝ)/4 ≤ Real.exp (-1332076643531/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027479646871/500000000000 : ℝ)/4 ≤ Real.exp ((999/8192 : ℝ)-(787986563953/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (999/8192 : ℝ) (1999/16384 : ℝ) (787986563953/1000000000000 : ℝ) (1027479646871/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0089; no trusted numerical premise.
theorem cover8_leaf0089_exp_radius : (998094469200659971/1000000000000000000 : ℝ) ≤ Real.exp ((-125/8192 : ℝ)/8) ∧ Real.exp ((-125/8192 : ℝ)/8) ≤ (249523617300164993/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-125/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0089_exp_lower : (920116462365114057/1000000000000000000 : ℝ) ≤ Real.exp ((-2664160877553/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664160877553/4000000000000 : ℝ)/8) ≤ (460058231182557029/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664160877553/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0089_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054955394209/1000000000000 : ℝ) ≤ 4*Real.exp (1999/16384 : ℝ)*Real.exp (-mu (radius 8 (125/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2054955394209/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (125/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0089_exp_radius
  have hrNumeric : (123107129549/125000000000 : ℝ) ≤ Real.exp (-125/8192 : ℝ) ∧ Real.exp (-125/8192 : ℝ) ≤ (984857036393/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123107129549/125000000000 : ℝ) ≤ (radius 8 (125/1024 : ℝ)) ∧ (radius 8 (125/1024 : ℝ)) ≤ (984857036393/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (125/1024 : ℝ)) (123107129549/125000000000 : ℝ) (984857036393/1000000000000 : ℝ) (173368445419/1000000000000 : ℝ) (86684222713/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (125/1024 : ℝ)) (123107129549/125000000000 : ℝ) (984857036393/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (125/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123107129549/125000000000 : ℝ) (984857036393/1000000000000 : ℝ) (248107129549/250000000000 : ℝ) (992428518197/1000000000000 : ℝ) (39695985417/40000000000 : ℝ) (496199817713/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (125/1024 : ℝ)) 1 (248107129549/250000000000 : ℝ) (992428518197/1000000000000 : ℝ) (39695985417/40000000000 : ℝ) (496199817713/500000000000 : ℝ) (99241407681/100000000000 : ℝ) (248103519203/250000000000 : ℝ) (198482815341/200000000000 : ℝ) (992414076707/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (125/1024 : ℝ)) 2 (99241407681/100000000000 : ℝ) (248103519203/250000000000 : ℝ) (198482815341/200000000000 : ℝ) (992414076707/1000000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (125/1024 : ℝ)) 3 (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (125/1024 : ℝ)) 4 (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (125/1024 : ℝ)) 5 (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (125/1024 : ℝ)) 6 (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (125/1024 : ℝ)) 7 (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (125/1024 : ℝ))) (173368445419/1000000000000 : ℝ) (86684222713/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (125/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (173368445419/1000000000000 : ℝ) (86684222713/500000000000 : ℝ) (586684222709/1000000000000 : ℝ) (586684222713/1000000000000 : ℝ) (52046920751/125000000000 : ℝ) (208187683009/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (125/1024 : ℝ))) 1 (586684222709/1000000000000 : ℝ) (586684222713/1000000000000 : ℝ) (52046920751/125000000000 : ℝ) (208187683009/500000000000 : ℝ) (250764897179/500000000000 : ℝ) (250764897183/500000000000 : ℝ) (494247769809/1000000000000 : ℝ) (247123884909/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (125/1024 : ℝ))) 2 (250764897179/500000000000 : ℝ) (250764897183/500000000000 : ℝ) (494247769809/1000000000000 : ℝ) (247123884909/500000000000 : ℝ) (497888782083/1000000000000 : ℝ) (124472195523/250000000000 : ℝ) (497875468721/1000000000000 : ℝ) (49787546873/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (125/1024 : ℝ))) 3 (497888782083/1000000000000 : ℝ) (124472195523/250000000000 : ℝ) (497875468721/1000000000000 : ℝ) (49787546873/100000000000 : ℝ) (248941062701/500000000000 : ℝ) (497882125411/1000000000000 : ℝ) (497882125357/1000000000000 : ℝ) (497882125367/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (125/1024 : ℝ))) 4 (248941062701/500000000000 : ℝ) (497882125411/1000000000000 : ℝ) (497882125357/1000000000000 : ℝ) (497882125367/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (125/1024 : ℝ))) 5 (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (125/1024 : ℝ))) 6 (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (125/1024 : ℝ))) 7 (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (125/1024 : ℝ)) hmem 8 (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (125/1024 : ℝ))) hcmem 8 (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (125/1024 : ℝ)) (992414076757/1000000000000 : ℝ) (24810351919/25000000000 : ℝ) (497882125379/1000000000000 : ℝ) (497882125389/1000000000000 : ℝ) (788049496713/1000000000000 : ℝ) (197012374183/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0089_exp_lower
  have heNumeric : (2054955394209/1000000000000 : ℝ)/4 ≤ Real.exp (-2664160877553/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054955394209/1000000000000 : ℝ)/4 ≤ Real.exp ((1999/16384 : ℝ)-(197012374183/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1999/16384 : ℝ) (125/1024 : ℝ) (197012374183/250000000000 : ℝ) (2054955394209/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0090; no trusted numerical premise.
theorem cover8_leaf0090_exp_radius : (249523379336013307/250000000000000000 : ℝ) ≤ Real.exp ((-2001/131072 : ℝ)/8) ∧ Real.exp ((-2001/131072 : ℝ)/8) ≤ (998093517344053229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2001/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0090_exp_lower : (36804649862929783/40000000000000000 : ℝ) ≤ Real.exp ((-333021047801/500000000000 : ℝ)/8) ∧ Real.exp ((-333021047801/500000000000 : ℝ)/8) ≤ (28753632705413893/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333021047801/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0090_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054951538677/1000000000000 : ℝ) ≤ 4*Real.exp (125/1024 : ℝ)*Real.exp (-mu (radius 8 (2001/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054951538677/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2001/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0090_exp_radius
  have hrNumeric : (492424761279/500000000000 : ℝ) ≤ Real.exp (-2001/131072 : ℝ) ∧ Real.exp (-2001/131072 : ℝ) ≤ (984849522559/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492424761279/500000000000 : ℝ) ≤ (radius 8 (2001/16384 : ℝ)) ∧ (radius 8 (2001/16384 : ℝ)) ≤ (984849522559/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2001/16384 : ℝ)) (492424761279/500000000000 : ℝ) (984849522559/1000000000000 : ℝ) (86705561983/500000000000 : ℝ) (173411123973/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2001/16384 : ℝ)) (492424761279/500000000000 : ℝ) (984849522559/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2001/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492424761279/500000000000 : ℝ) (984849522559/1000000000000 : ℝ) (992424761279/1000000000000 : ℝ) (3101327379/3125000000 : ℝ) (242284143/244140625 : ℝ) (992395849729/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2001/16384 : ℝ)) 1 (992424761279/1000000000000 : ℝ) (3101327379/3125000000 : ℝ) (242284143/244140625 : ℝ) (992395849729/1000000000000 : ℝ) (992410305503/1000000000000 : ℝ) (198482061101/200000000000 : ℝ) (496205152699/500000000000 : ℝ) (4962051527/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2001/16384 : ℝ)) 2 (992410305503/1000000000000 : ℝ) (198482061101/200000000000 : ℝ) (496205152699/500000000000 : ℝ) (4962051527/5000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2001/16384 : ℝ)) 3 (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2001/16384 : ℝ)) 4 (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2001/16384 : ℝ)) 5 (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2001/16384 : ℝ)) 6 (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2001/16384 : ℝ)) 7 (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2001/16384 : ℝ))) (86705561983/500000000000 : ℝ) (173411123973/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2001/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (86705561983/500000000000 : ℝ) (173411123973/1000000000000 : ℝ) (586705561983/1000000000000 : ℝ) (586705561987/1000000000000 : ℝ) (416426612941/1000000000000 : ℝ) (8328532259/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2001/16384 : ℝ))) 1 (586705561983/1000000000000 : ℝ) (586705561987/1000000000000 : ℝ) (416426612941/1000000000000 : ℝ) (8328532259/20000000000 : ℝ) (250783043731/500000000000 : ℝ) (501566087469/1000000000000 : ℝ) (30892948349/62500000000 : ℝ) (61785896699/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2001/16384 : ℝ))) 2 (250783043731/500000000000 : ℝ) (501566087469/1000000000000 : ℝ) (30892948349/62500000000 : ℝ) (61785896699/125000000000 : ℝ) (497926630523/1000000000000 : ℝ) (497926630531/1000000000000 : ℝ) (497913329543/1000000000000 : ℝ) (31119583097/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2001/16384 : ℝ))) 3 (497926630523/1000000000000 : ℝ) (497926630531/1000000000000 : ℝ) (497913329543/1000000000000 : ℝ) (31119583097/62500000000 : ℝ) (497919980033/1000000000000 : ℝ) (248959990021/500000000000 : ℝ) (124479994997/250000000000 : ℝ) (248959989999/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2001/16384 : ℝ))) 4 (497919980033/1000000000000 : ℝ) (248959990021/500000000000 : ℝ) (124479994997/250000000000 : ℝ) (248959989999/500000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2001/16384 : ℝ))) 5 (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2001/16384 : ℝ))) 6 (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2001/16384 : ℝ))) 7 (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2001/16384 : ℝ)) hmem 8 (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2001/16384 : ℝ))) hcmem 8 (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2001/16384 : ℝ)) (19848206109/20000000000 : ℝ) (992410305453/1000000000000 : ℝ) (49791998001/100000000000 : ℝ) (24895999001/50000000000 : ℝ) (788112408083/1000000000000 : ℝ) (394056204051/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0090_exp_lower
  have heNumeric : (2054951538677/1000000000000 : ℝ)/4 ≤ Real.exp (-333021047801/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054951538677/1000000000000 : ℝ)/4 ≤ Real.exp ((125/1024 : ℝ)-(394056204051/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (125/1024 : ℝ) (2001/16384 : ℝ) (394056204051/500000000000 : ℝ) (2054951538677/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0091; no trusted numerical premise.
theorem cover8_leaf0091_exp_radius : (499046282744177123/500000000000000000 : ℝ) ≤ Real.exp ((-1001/65536 : ℝ)/8) ∧ Real.exp ((-1001/65536 : ℝ)/8) ≤ (998092565488354247/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1001/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0091_exp_lower : (460058016621023/500000000000000 : ℝ) ≤ Real.exp ((-2664175801687/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664175801687/4000000000000 : ℝ)/8) ≤ (920116033242046001/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664175801687/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0091_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410989545423/200000000000 : ℝ) ≤ 4*Real.exp (2001/16384 : ℝ)*Real.exp (-mu (radius 8 (1001/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (410989545423/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1001/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0091_exp_radius
  have hrNumeric : (984842008781/1000000000000 : ℝ) ≤ Real.exp (-1001/65536 : ℝ) ∧ Real.exp (-1001/65536 : ℝ) ≤ (492421004391/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984842008781/1000000000000 : ℝ) ≤ (radius 8 (1001/8192 : ℝ)) ∧ (radius 8 (1001/8192 : ℝ)) ≤ (492421004391/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1001/8192 : ℝ)) (984842008781/1000000000000 : ℝ) (492421004391/500000000000 : ℝ) (173453791363/1000000000000 : ℝ) (173453791369/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1001/8192 : ℝ)) (984842008781/1000000000000 : ℝ) (492421004391/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1001/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984842008781/1000000000000 : ℝ) (492421004391/500000000000 : ℝ) (99242100439/100000000000 : ℝ) (992421004391/1000000000000 : ℝ) (198478412809/200000000000 : ℝ) (992392064047/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1001/8192 : ℝ)) 1 (99242100439/100000000000 : ℝ) (992421004391/1000000000000 : ℝ) (198478412809/200000000000 : ℝ) (992392064047/1000000000000 : ℝ) (992406534217/1000000000000 : ℝ) (992406534219/1000000000000 : ℝ) (31012704191/31250000000 : ℝ) (496203267057/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1001/8192 : ℝ)) 2 (992406534217/1000000000000 : ℝ) (992406534219/1000000000000 : ℝ) (31012704191/31250000000 : ℝ) (496203267057/500000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1001/8192 : ℝ)) 3 (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1001/8192 : ℝ)) 4 (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1001/8192 : ℝ)) 5 (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1001/8192 : ℝ)) 6 (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1001/8192 : ℝ)) 7 (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1001/8192 : ℝ))) (173453791363/1000000000000 : ℝ) (173453791369/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1001/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (173453791363/1000000000000 : ℝ) (173453791369/1000000000000 : ℝ) (586726895681/1000000000000 : ℝ) (117345379137/200000000000 : ℝ) (208238920091/500000000000 : ℝ) (41647784019/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1001/8192 : ℝ))) 1 (586726895681/1000000000000 : ℝ) (117345379137/200000000000 : ℝ) (208238920091/500000000000 : ℝ) (41647784019/100000000000 : ℝ) (501602367931/1000000000000 : ℝ) (250801183969/500000000000 : ℝ) (98865312479/200000000000 : ℝ) (494326562403/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1001/8192 : ℝ))) 2 (501602367931/1000000000000 : ℝ) (250801183969/500000000000 : ℝ) (98865312479/200000000000 : ℝ) (494326562403/1000000000000 : ℝ) (497964465163/1000000000000 : ℝ) (497964465171/1000000000000 : ℝ) (9959023531/20000000000 : ℝ) (497951176559/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1001/8192 : ℝ))) 3 (497964465163/1000000000000 : ℝ) (497964465171/1000000000000 : ℝ) (9959023531/20000000000 : ℝ) (497951176559/1000000000000 : ℝ) (62244727607/125000000000 : ℝ) (99591564173/200000000000 : ℝ) (124489455203/250000000000 : ℝ) (497957820821/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1001/8192 : ℝ))) 4 (62244727607/125000000000 : ℝ) (99591564173/200000000000 : ℝ) (124489455203/250000000000 : ℝ) (497957820821/1000000000000 : ℝ) (248978910417/500000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1001/8192 : ℝ))) 5 (248978910417/500000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1001/8192 : ℝ))) 6 (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1001/8192 : ℝ))) 7 (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1001/8192 : ℝ)) hmem 8 (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1001/8192 : ℝ))) hcmem 8 (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1001/8192 : ℝ)) (248101633541/250000000000 : ℝ) (992406534167/1000000000000 : ℝ) (497957820833/1000000000000 : ℝ) (497957820843/1000000000000 : ℝ) (788175298059/1000000000000 : ℝ) (394087649039/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0091_exp_lower
  have heNumeric : (410989545423/200000000000 : ℝ)/4 ≤ Real.exp (-2664175801687/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410989545423/200000000000 : ℝ)/4 ≤ Real.exp ((2001/16384 : ℝ)-(394087649039/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2001/16384 : ℝ) (1001/8192 : ℝ) (394087649039/500000000000 : ℝ) (410989545423/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0092; no trusted numerical premise.
theorem cover8_leaf0092_exp_radius : (62380725852097689/62500000000000000 : ℝ) ≤ Real.exp ((-2003/131072 : ℝ)/8) ∧ Real.exp ((-2003/131072 : ℝ)/8) ≤ (39923664545342521/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2003/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0092_exp_lower : (14376809724515411/15625000000000000 : ℝ) ≤ Real.exp ((-1332091567739/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332091567739/2000000000000 : ℝ)/8) ≤ (184023164473797261/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332091567739/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0092_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51373598987/25000000000 : ℝ) ≤ 4*Real.exp (1001/8192 : ℝ)*Real.exp (-mu (radius 8 (2003/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (51373598987/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2003/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0092_exp_radius
  have hrNumeric : (984834495061/1000000000000 : ℝ) ≤ Real.exp (-2003/131072 : ℝ) ∧ Real.exp (-2003/131072 : ℝ) ≤ (492417247531/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984834495061/1000000000000 : ℝ) ≤ (radius 8 (2003/16384 : ℝ)) ∧ (radius 8 (2003/16384 : ℝ)) ≤ (492417247531/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2003/16384 : ℝ)) (984834495061/1000000000000 : ℝ) (492417247531/500000000000 : ℝ) (173496447617/1000000000000 : ℝ) (21687055953/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2003/16384 : ℝ)) (984834495061/1000000000000 : ℝ) (492417247531/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2003/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984834495061/1000000000000 : ℝ) (492417247531/500000000000 : ℝ) (99241724753/100000000000 : ℝ) (992417247531/1000000000000 : ℝ) (992388278377/1000000000000 : ℝ) (496194139189/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2003/16384 : ℝ)) 1 (99241724753/100000000000 : ℝ) (992417247531/1000000000000 : ℝ) (992388278377/1000000000000 : ℝ) (496194139189/500000000000 : ℝ) (992402762953/1000000000000 : ℝ) (198480552591/200000000000 : ℝ) (992402762847/1000000000000 : ℝ) (992402762849/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2003/16384 : ℝ)) 2 (992402762953/1000000000000 : ℝ) (198480552591/200000000000 : ℝ) (992402762847/1000000000000 : ℝ) (992402762849/1000000000000 : ℝ) (9924027629/10000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2003/16384 : ℝ)) 3 (9924027629/10000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2003/16384 : ℝ)) 4 (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2003/16384 : ℝ)) 5 (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2003/16384 : ℝ)) 6 (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2003/16384 : ℝ)) 7 (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2003/16384 : ℝ))) (173496447617/1000000000000 : ℝ) (21687055953/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2003/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (173496447617/1000000000000 : ℝ) (21687055953/125000000000 : ℝ) (9167940997/15625000000 : ℝ) (146687055953/250000000000 : ℝ) (208264523873/500000000000 : ℝ) (104132261939/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2003/16384 : ℝ))) 1 (9167940997/15625000000 : ℝ) (146687055953/250000000000 : ℝ) (208264523873/500000000000 : ℝ) (104132261939/250000000000 : ℝ) (501638635777/1000000000000 : ℝ) (62704829473/125000000000 : ℝ) (98873187251/200000000000 : ℝ) (494365936263/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2003/16384 : ℝ))) 2 (501638635777/1000000000000 : ℝ) (62704829473/125000000000 : ℝ) (98873187251/200000000000 : ℝ) (494365936263/1000000000000 : ℝ) (7781285719/15625000000 : ℝ) (62250285753/125000000000 : ℝ) (99597801951/200000000000 : ℝ) (124497252441/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2003/16384 : ℝ))) 3 (7781285719/15625000000 : ℝ) (62250285753/125000000000 : ℝ) (99597801951/200000000000 : ℝ) (124497252441/250000000000 : ℝ) (99599129577/200000000000 : ℝ) (248997823947/500000000000 : ℝ) (497995647841/1000000000000 : ℝ) (9959912957/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2003/16384 : ℝ))) 4 (99599129577/200000000000 : ℝ) (248997823947/500000000000 : ℝ) (497995647841/1000000000000 : ℝ) (9959912957/20000000000 : ℝ) (497995647863/1000000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2003/16384 : ℝ))) 5 (497995647863/1000000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2003/16384 : ℝ))) 6 (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2003/16384 : ℝ))) 7 (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2003/16384 : ℝ)) hmem 8 (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2003/16384 : ℝ))) hcmem 8 (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2003/16384 : ℝ)) (992402762899/1000000000000 : ℝ) (496201381451/500000000000 : ℝ) (248997823931/500000000000 : ℝ) (3890590999/7812500000 : ℝ) (788238166663/1000000000000 : ℝ) (394119083341/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0092_exp_lower
  have heNumeric : (51373598987/25000000000 : ℝ)/4 ≤ Real.exp (-1332091567739/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51373598987/25000000000 : ℝ)/4 ≤ Real.exp ((1001/8192 : ℝ)-(394119083341/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1001/8192 : ℝ) (2003/16384 : ℝ) (394119083341/500000000000 : ℝ) (51373598987/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0093; no trusted numerical premise.
theorem cover8_leaf0093_exp_radius : (24952266544491989/25000000000000000 : ℝ) ≤ Real.exp ((-501/32768 : ℝ)/8) ∧ Real.exp ((-501/32768 : ℝ)/8) ≤ (998090661779679561/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-501/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0093_exp_lower : (115014451744128583/125000000000000000 : ℝ) ≤ Real.exp ((-2664190383817/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664190383817/4000000000000 : ℝ)/8) ≤ (184023122790605733/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664190383817/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0093_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (8219760943/4000000000 : ℝ) ≤ 4*Real.exp (2003/16384 : ℝ)*Real.exp (-mu (radius 8 (501/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (8219760943/4000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (501/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0093_exp_radius
  have hrNumeric : (984826981399/1000000000000 : ℝ) ≤ Real.exp (-501/32768 : ℝ) ∧ Real.exp (-501/32768 : ℝ) ≤ (4924134907/5000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984826981399/1000000000000 : ℝ) ≤ (radius 8 (501/4096 : ℝ)) ∧ (radius 8 (501/4096 : ℝ)) ≤ (4924134907/5000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (501/4096 : ℝ)) (984826981399/1000000000000 : ℝ) (4924134907/5000000000 : ℝ) (43384773183/250000000000 : ℝ) (173539092739/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (501/4096 : ℝ)) (984826981399/1000000000000 : ℝ) (4924134907/5000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (501/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984826981399/1000000000000 : ℝ) (4924134907/5000000000 : ℝ) (992413490699/1000000000000 : ℝ) (9924134907/10000000000 : ℝ) (992384492723/1000000000000 : ℝ) (39695379709/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (501/4096 : ℝ)) 1 (992413490699/1000000000000 : ℝ) (9924134907/10000000000 : ℝ) (992384492723/1000000000000 : ℝ) (39695379709/40000000000 : ℝ) (992398991711/1000000000000 : ℝ) (992398991713/1000000000000 : ℝ) (198479798321/200000000000 : ℝ) (992398991607/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (501/4096 : ℝ)) 2 (992398991711/1000000000000 : ℝ) (992398991713/1000000000000 : ℝ) (198479798321/200000000000 : ℝ) (992398991607/1000000000000 : ℝ) (496199495829/500000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (501/4096 : ℝ)) 3 (496199495829/500000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (501/4096 : ℝ)) 4 (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (501/4096 : ℝ)) 5 (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (501/4096 : ℝ)) 6 (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (501/4096 : ℝ)) 7 (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (501/4096 : ℝ))) (43384773183/250000000000 : ℝ) (173539092739/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (501/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43384773183/250000000000 : ℝ) (173539092739/1000000000000 : ℝ) (293384773183/500000000000 : ℝ) (58676954637/100000000000 : ℝ) (416580235647/1000000000000 : ℝ) (52072529457/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (501/4096 : ℝ))) 1 (293384773183/500000000000 : ℝ) (58676954637/100000000000 : ℝ) (416580235647/1000000000000 : ℝ) (52072529457/125000000000 : ℝ) (250837445503/500000000000 : ℝ) (501674891013/1000000000000 : ℝ) (494405295173/1000000000000 : ℝ) (494405295181/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (501/4096 : ℝ))) 2 (250837445503/500000000000 : ℝ) (501674891013/1000000000000 : ℝ) (494405295173/1000000000000 : ℝ) (494405295181/1000000000000 : ℝ) (498040093089/1000000000000 : ℝ) (498040093097/1000000000000 : ℝ) (99605365833/200000000000 : ℝ) (249013414587/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (501/4096 : ℝ))) 3 (498040093089/1000000000000 : ℝ) (498040093097/1000000000000 : ℝ) (99605365833/200000000000 : ℝ) (249013414587/500000000000 : ℝ) (498033461127/1000000000000 : ℝ) (31127091321/62500000000 : ℝ) (249016730541/500000000000 : ℝ) (124508365273/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (501/4096 : ℝ))) 4 (498033461127/1000000000000 : ℝ) (31127091321/62500000000 : ℝ) (249016730541/500000000000 : ℝ) (124508365273/250000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (501/4096 : ℝ))) 5 (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (501/4096 : ℝ))) 6 (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (501/4096 : ℝ))) 7 (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (501/4096 : ℝ)) hmem 8 (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (501/4096 : ℝ))) hcmem 8 (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (501/4096 : ℝ)) (992398991657/1000000000000 : ℝ) (49619949583/50000000000 : ℝ) (31127091319/62500000000 : ℝ) (249016730557/500000000000 : ℝ) (49268813369/62500000000 : ℝ) (788301013923/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0093_exp_lower
  have heNumeric : (8219760943/4000000000 : ℝ)/4 ≤ Real.exp (-2664190383817/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (8219760943/4000000000 : ℝ)/4 ≤ Real.exp ((2003/16384 : ℝ)-(788301013923/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2003/16384 : ℝ) (501/4096 : ℝ) (788301013923/1000000000000 : ℝ) (8219760943/4000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0094; no trusted numerical premise.
theorem cover8_leaf0094_exp_radius : (199617941985340771/200000000000000000 : ℝ) ≤ Real.exp ((-2005/131072 : ℝ)/8) ∧ Real.exp ((-2005/131072 : ℝ)/8) ≤ (62380606870418991/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2005/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0094_exp_lower : (920115407991066023/1000000000000000000 : ℝ) ≤ Real.exp ((-666049386703/1000000000000 : ℝ)/8) ∧ Real.exp ((-666049386703/1000000000000 : ℝ)/8) ≤ (115014425998883253/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666049386703/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0094_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64216767371/31250000000 : ℝ) ≤ 4*Real.exp (501/4096 : ℝ)*Real.exp (-mu (radius 8 (2005/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (64216767371/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2005/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0094_exp_radius
  have hrNumeric : (492409733897/500000000000 : ℝ) ≤ Real.exp (-2005/131072 : ℝ) ∧ Real.exp (-2005/131072 : ℝ) ≤ (196963893559/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492409733897/500000000000 : ℝ) ≤ (radius 8 (2005/16384 : ℝ)) ∧ (radius 8 (2005/16384 : ℝ)) ≤ (196963893559/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2005/16384 : ℝ)) (492409733897/500000000000 : ℝ) (196963893559/200000000000 : ℝ) (86790863361/500000000000 : ℝ) (173581726729/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2005/16384 : ℝ)) (492409733897/500000000000 : ℝ) (196963893559/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2005/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492409733897/500000000000 : ℝ) (196963893559/200000000000 : ℝ) (992409733897/1000000000000 : ℝ) (496204866949/500000000000 : ℝ) (248095176771/250000000000 : ℝ) (496190353543/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2005/16384 : ℝ)) 1 (992409733897/1000000000000 : ℝ) (496204866949/500000000000 : ℝ) (248095176771/250000000000 : ℝ) (496190353543/500000000000 : ℝ) (99239522049/100000000000 : ℝ) (248098805123/250000000000 : ℝ) (31012350637/31250000000 : ℝ) (496197610193/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2005/16384 : ℝ)) 2 (99239522049/100000000000 : ℝ) (248098805123/250000000000 : ℝ) (31012350637/31250000000 : ℝ) (496197610193/500000000000 : ℝ) (992395220437/1000000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2005/16384 : ℝ)) 3 (992395220437/1000000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2005/16384 : ℝ)) 4 (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2005/16384 : ℝ)) 5 (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2005/16384 : ℝ)) 6 (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2005/16384 : ℝ)) 7 (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2005/16384 : ℝ))) (86790863361/500000000000 : ℝ) (173581726729/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2005/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (86790863361/500000000000 : ℝ) (173581726729/1000000000000 : ℝ) (586790863361/1000000000000 : ℝ) (117358172673/200000000000 : ℝ) (416631403907/1000000000000 : ℝ) (104157850979/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2005/16384 : ℝ))) 1 (586790863361/1000000000000 : ℝ) (117358172673/200000000000 : ℝ) (416631403907/1000000000000 : ℝ) (104157850979/250000000000 : ℝ) (250855566817/500000000000 : ℝ) (501711133641/1000000000000 : ℝ) (494444639167/1000000000000 : ℝ) (19777785567/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2005/16384 : ℝ))) 2 (250855566817/500000000000 : ℝ) (501711133641/1000000000000 : ℝ) (494444639167/1000000000000 : ℝ) (19777785567/40000000000 : ℝ) (311298679/625000000 : ℝ) (62259735801/125000000000 : ℝ) (498064634797/1000000000000 : ℝ) (99612926961/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2005/16384 : ℝ))) 3 (311298679/625000000 : ℝ) (62259735801/125000000000 : ℝ) (498064634797/1000000000000 : ℝ) (99612926961/200000000000 : ℝ) (249035630299/500000000000 : ℝ) (498071260607/1000000000000 : ℝ) (249035630277/500000000000 : ℝ) (498071260563/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2005/16384 : ℝ))) 4 (249035630299/500000000000 : ℝ) (498071260607/1000000000000 : ℝ) (249035630277/500000000000 : ℝ) (498071260563/1000000000000 : ℝ) (15564726893/31250000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2005/16384 : ℝ))) 5 (15564726893/31250000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2005/16384 : ℝ))) 6 (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2005/16384 : ℝ))) 7 (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2005/16384 : ℝ)) hmem 8 (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2005/16384 : ℝ))) hcmem 8 (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2005/16384 : ℝ)) (248098805109/250000000000 : ℝ) (992395220439/1000000000000 : ℝ) (19922850423/40000000000 : ℝ) (99614252117/200000000000 : ℝ) (12318184997/15625000000 : ℝ) (197090959957/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0094_exp_lower
  have heNumeric : (64216767371/31250000000 : ℝ)/4 ≤ Real.exp (-666049386703/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64216767371/31250000000 : ℝ)/4 ≤ Real.exp ((501/4096 : ℝ)-(197090959957/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (501/4096 : ℝ) (2005/16384 : ℝ) (197090959957/250000000000 : ℝ) (64216767371/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0095; no trusted numerical premise.
theorem cover8_leaf0095_exp_radius : (998088758074635907/1000000000000000000 : ℝ) ≤ Real.exp ((-1003/65536 : ℝ)/8) ∧ Real.exp ((-1003/65536 : ℝ)/8) ≤ (249522189518658977/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1003/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0095_exp_lower : (920115204480911459/1000000000000000000 : ℝ) ≤ Real.exp ((-2664204624539/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664204624539/4000000000000 : ℝ)/8) ≤ (46005760224045573/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664204624539/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0095_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410986583961/200000000000 : ℝ) ≤ 4*Real.exp (2005/16384 : ℝ)*Real.exp (-mu (radius 8 (1003/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (410986583961/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1003/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0095_exp_radius
  have hrNumeric : (492405977123/500000000000 : ℝ) ≤ Real.exp (-1003/65536 : ℝ) ∧ Real.exp (-1003/65536 : ℝ) ≤ (984811954247/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492405977123/500000000000 : ℝ) ≤ (radius 8 (1003/8192 : ℝ)) ∧ (radius 8 (1003/8192 : ℝ)) ≤ (984811954247/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1003/8192 : ℝ)) (492405977123/500000000000 : ℝ) (984811954247/1000000000000 : ℝ) (86812174797/500000000000 : ℝ) (173624349601/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1003/8192 : ℝ)) (492405977123/500000000000 : ℝ) (984811954247/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1003/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492405977123/500000000000 : ℝ) (984811954247/1000000000000 : ℝ) (992405977123/1000000000000 : ℝ) (248101494281/250000000000 : ℝ) (992376921459/1000000000000 : ℝ) (992376921461/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1003/8192 : ℝ)) 1 (992405977123/1000000000000 : ℝ) (248101494281/250000000000 : ℝ) (992376921459/1000000000000 : ℝ) (992376921461/1000000000000 : ℝ) (992391449291/1000000000000 : ℝ) (992391449293/1000000000000 : ℝ) (31012232787/31250000000 : ℝ) (992391449187/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1003/8192 : ℝ)) 2 (992391449291/1000000000000 : ℝ) (992391449293/1000000000000 : ℝ) (31012232787/31250000000 : ℝ) (992391449187/1000000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1003/8192 : ℝ)) 3 (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1003/8192 : ℝ)) 4 (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1003/8192 : ℝ)) 5 (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1003/8192 : ℝ)) 6 (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1003/8192 : ℝ)) 7 (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1003/8192 : ℝ))) (86812174797/500000000000 : ℝ) (173624349601/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1003/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (86812174797/500000000000 : ℝ) (173624349601/1000000000000 : ℝ) (586812174797/1000000000000 : ℝ) (586812174801/1000000000000 : ℝ) (416682552543/1000000000000 : ℝ) (52085319069/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1003/8192 : ℝ))) 1 (586812174797/1000000000000 : ℝ) (586812174801/1000000000000 : ℝ) (416682552543/1000000000000 : ℝ) (52085319069/125000000000 : ℝ) (50174736367/100000000000 : ℝ) (501747363677/1000000000000 : ℝ) (494483968251/1000000000000 : ℝ) (494483968259/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1003/8192 : ℝ))) 2 (50174736367/100000000000 : ℝ) (501747363677/1000000000000 : ℝ) (494483968251/1000000000000 : ℝ) (494483968259/1000000000000 : ℝ) (12452891649/25000000000 : ℝ) (31132229123/62500000000 : ℝ) (249051213331/500000000000 : ℝ) (49810242667/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1003/8192 : ℝ))) 3 (12452891649/25000000000 : ℝ) (31132229123/62500000000 : ℝ) (249051213331/500000000000 : ℝ) (49810242667/100000000000 : ℝ) (498109046311/1000000000000 : ℝ) (498109046319/1000000000000 : ℝ) (498109046267/1000000000000 : ℝ) (124527261569/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1003/8192 : ℝ))) 4 (498109046311/1000000000000 : ℝ) (498109046319/1000000000000 : ℝ) (498109046267/1000000000000 : ℝ) (124527261569/250000000000 : ℝ) (498109046289/1000000000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1003/8192 : ℝ))) 5 (498109046289/1000000000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1003/8192 : ℝ))) 6 (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1003/8192 : ℝ))) 7 (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1003/8192 : ℝ)) hmem 8 (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1003/8192 : ℝ))) hcmem 8 (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1003/8192 : ℝ)) (992391449237/1000000000000 : ℝ) (24809786231/25000000000 : ℝ) (31131815393/62500000000 : ℝ) (249054523149/500000000000 : ℝ) (197106661099/250000000000 : ℝ) (12319166319/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0095_exp_lower
  have heNumeric : (410986583961/200000000000 : ℝ)/4 ≤ Real.exp (-2664204624539/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410986583961/200000000000 : ℝ)/4 ≤ Real.exp ((2005/16384 : ℝ)-(12319166319/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2005/16384 : ℝ) (1003/8192 : ℝ) (12319166319/15625000000 : ℝ) (410986583961/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0096; no trusted numerical premise.
theorem cover8_leaf0096_exp_radius : (199617561244695143/200000000000000000 : ℝ) ≤ Real.exp ((-2007/131072 : ℝ)/8) ∧ Real.exp ((-2007/131072 : ℝ)/8) ≤ (249521951555868929/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2007/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0096_exp_lower : (920115003421413201/1000000000000000000 : ℝ) ≤ Real.exp ((-1332105808519/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332105808519/2000000000000 : ℝ)/8) ≤ (460057501710706601/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332105808519/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0096_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054929327529/1000000000000 : ℝ) ≤ 4*Real.exp (1003/8192 : ℝ)*Real.exp (-mu (radius 8 (2007/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054929327529/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2007/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0096_exp_radius
  have hrNumeric : (246201110189/250000000000 : ℝ) ≤ Real.exp (-2007/131072 : ℝ) ∧ Real.exp (-2007/131072 : ℝ) ≤ (984804440757/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246201110189/250000000000 : ℝ) ≤ (radius 8 (2007/16384 : ℝ)) ∧ (radius 8 (2007/16384 : ℝ)) ≤ (984804440757/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2007/16384 : ℝ)) (246201110189/250000000000 : ℝ) (984804440757/1000000000000 : ℝ) (21708370169/125000000000 : ℝ) (86833480679/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2007/16384 : ℝ)) (246201110189/250000000000 : ℝ) (984804440757/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2007/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246201110189/250000000000 : ℝ) (984804440757/1000000000000 : ℝ) (496201110189/500000000000 : ℝ) (992402220379/1000000000000 : ℝ) (992373135849/1000000000000 : ℝ) (992373135851/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2007/16384 : ℝ)) 1 (496201110189/500000000000 : ℝ) (992402220379/1000000000000 : ℝ) (992373135849/1000000000000 : ℝ) (992373135851/1000000000000 : ℝ) (992387678113/1000000000000 : ℝ) (198477535623/200000000000 : ℝ) (496193839003/500000000000 : ℝ) (992387678009/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2007/16384 : ℝ)) 2 (992387678113/1000000000000 : ℝ) (198477535623/200000000000 : ℝ) (496193839003/500000000000 : ℝ) (992387678009/1000000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2007/16384 : ℝ)) 3 (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2007/16384 : ℝ)) 4 (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2007/16384 : ℝ)) 5 (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2007/16384 : ℝ)) 6 (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2007/16384 : ℝ)) 7 (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2007/16384 : ℝ))) (21708370169/125000000000 : ℝ) (86833480679/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2007/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21708370169/125000000000 : ℝ) (86833480679/500000000000 : ℝ) (146708370169/250000000000 : ℝ) (586833480679/1000000000000 : ℝ) (208366840783/500000000000 : ℝ) (208366840787/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2007/16384 : ℝ))) 1 (146708370169/250000000000 : ℝ) (586833480679/1000000000000 : ℝ) (208366840783/500000000000 : ℝ) (208366840787/500000000000 : ℝ) (501783581121/1000000000000 : ℝ) (501783581127/1000000000000 : ℝ) (482932893/976562500 : ℝ) (12363082061/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2007/16384 : ℝ))) 2 (501783581121/1000000000000 : ℝ) (501783581127/1000000000000 : ℝ) (482932893/976562500 : ℝ) (12363082061/25000000000 : ℝ) (15567294743/31250000000 : ℝ) (62269178973/125000000000 : ℝ) (15566881399/31250000000 : ℝ) (62267525597/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2007/16384 : ℝ))) 3 (15567294743/31250000000 : ℝ) (62269178973/125000000000 : ℝ) (15566881399/31250000000 : ℝ) (62267525597/125000000000 : ℝ) (15567088071/31250000000 : ℝ) (12453670457/25000000000 : ℝ) (124536704557/250000000000 : ℝ) (498146818237/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2007/16384 : ℝ))) 4 (15567088071/31250000000 : ℝ) (12453670457/25000000000 : ℝ) (124536704557/250000000000 : ℝ) (498146818237/1000000000000 : ℝ) (1992587273/4000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2007/16384 : ℝ))) 5 (1992587273/4000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2007/16384 : ℝ))) 6 (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2007/16384 : ℝ))) 7 (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2007/16384 : ℝ)) hmem 8 (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2007/16384 : ℝ))) hcmem 8 (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2007/16384 : ℝ)) (992387678059/1000000000000 : ℝ) (496193839031/500000000000 : ℝ) (498146818249/1000000000000 : ℝ) (498146818259/1000000000000 : ℝ) (394244713839/500000000000 : ℝ) (788489427697/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0096_exp_lower
  have heNumeric : (2054929327529/1000000000000 : ℝ)/4 ≤ Real.exp (-1332105808519/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054929327529/1000000000000 : ℝ)/4 ≤ Real.exp ((1003/8192 : ℝ)-(788489427697/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1003/8192 : ℝ) (2007/16384 : ℝ) (788489427697/1000000000000 : ℝ) (2054929327529/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0097; no trusted numerical premise.
theorem cover8_leaf0097_exp_radius : (998086854373223279/1000000000000000000 : ℝ) ≤ Real.exp ((-251/16384 : ℝ)/8) ∧ Real.exp ((-251/16384 : ℝ)/8) ≤ (12476085679665291/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-251/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0097_exp_lower : (184022960961892851/200000000000000000 : ℝ) ≤ Real.exp ((-2664218524417/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664218524417/4000000000000 : ℝ)/8) ≤ (14376793825147879/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664218524417/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0097_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513731444747/250000000000 : ℝ) ≤ 4*Real.exp (2007/16384 : ℝ)*Real.exp (-mu (radius 8 (251/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (513731444747/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (251/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0097_exp_radius
  have hrNumeric : (984796927323/1000000000000 : ℝ) ≤ Real.exp (-251/16384 : ℝ) ∧ Real.exp (-251/16384 : ℝ) ≤ (246199231831/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984796927323/1000000000000 : ℝ) ≤ (radius 8 (251/2048 : ℝ)) ∧ (radius 8 (251/2048 : ℝ)) ≤ (246199231831/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (251/2048 : ℝ)) (984796927323/1000000000000 : ℝ) (246199231831/250000000000 : ℝ) (21713695251/125000000000 : ℝ) (34741912403/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (251/2048 : ℝ)) (984796927323/1000000000000 : ℝ) (246199231831/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (251/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984796927323/1000000000000 : ℝ) (246199231831/250000000000 : ℝ) (992398463661/1000000000000 : ℝ) (496199231831/500000000000 : ℝ) (992369350253/1000000000000 : ℝ) (198473870051/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (251/2048 : ℝ)) 1 (992398463661/1000000000000 : ℝ) (496199231831/500000000000 : ℝ) (992369350253/1000000000000 : ℝ) (198473870051/200000000000 : ℝ) (992383906957/1000000000000 : ℝ) (992383906959/1000000000000 : ℝ) (19847678137/20000000000 : ℝ) (248095976713/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (251/2048 : ℝ)) 2 (992383906957/1000000000000 : ℝ) (992383906959/1000000000000 : ℝ) (19847678137/20000000000 : ℝ) (248095976713/250000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (251/2048 : ℝ)) 3 (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (251/2048 : ℝ)) 4 (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (251/2048 : ℝ)) 5 (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (251/2048 : ℝ)) 6 (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (251/2048 : ℝ)) 7 (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (251/2048 : ℝ))) (21713695251/125000000000 : ℝ) (34741912403/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (251/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21713695251/125000000000 : ℝ) (34741912403/200000000000 : ℝ) (146713695251/250000000000 : ℝ) (36678423813/62500000000 : ℝ) (208392395499/500000000000 : ℝ) (13024524719/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (251/2048 : ℝ))) 1 (146713695251/250000000000 : ℝ) (36678423813/62500000000 : ℝ) (208392395499/500000000000 : ℝ) (13024524719/31250000000 : ℝ) (501819786001/1000000000000 : ℝ) (62727473251/125000000000 : ℝ) (494562581729/1000000000000 : ℝ) (247281290869/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (251/2048 : ℝ))) 2 (501819786001/1000000000000 : ℝ) (62727473251/125000000000 : ℝ) (494562581729/1000000000000 : ℝ) (247281290869/500000000000 : ℝ) (99638236773/200000000000 : ℝ) (498191183873/1000000000000 : ℝ) (49817796913/100000000000 : ℝ) (498177969139/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (251/2048 : ℝ))) 3 (99638236773/200000000000 : ℝ) (498191183873/1000000000000 : ℝ) (49817796913/100000000000 : ℝ) (498177969139/1000000000000 : ℝ) (498184576497/1000000000000 : ℝ) (249092288253/500000000000 : ℝ) (498184576453/1000000000000 : ℝ) (498184576463/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (251/2048 : ℝ))) 4 (498184576497/1000000000000 : ℝ) (249092288253/500000000000 : ℝ) (498184576453/1000000000000 : ℝ) (498184576463/1000000000000 : ℝ) (19927383059/40000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (251/2048 : ℝ))) 5 (19927383059/40000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (251/2048 : ℝ))) 6 (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (251/2048 : ℝ))) 7 (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (251/2048 : ℝ)) hmem 8 (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (251/2048 : ℝ))) hcmem 8 (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (251/2048 : ℝ)) (992383906903/1000000000000 : ℝ) (496191953453/500000000000 : ℝ) (249092288237/500000000000 : ℝ) (99636915297/200000000000 : ℝ) (788552189677/1000000000000 : ℝ) (394276094849/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0097_exp_lower
  have heNumeric : (513731444747/250000000000 : ℝ)/4 ≤ Real.exp (-2664218524417/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513731444747/250000000000 : ℝ)/4 ≤ Real.exp ((2007/16384 : ℝ)-(394276094849/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2007/16384 : ℝ) (251/2048 : ℝ) (394276094849/500000000000 : ℝ) (513731444747/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0098; no trusted numerical premise.
theorem cover8_leaf0098_exp_radius : (499042951261939299/500000000000000000 : ℝ) ≤ Real.exp ((-2009/131072 : ℝ)/8) ∧ Real.exp ((-2009/131072 : ℝ)/8) ≤ (998085902523878599/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2009/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0098_exp_lower : (460057304321611403/500000000000000000 : ℝ) ≤ Real.exp ((-133211267337/200000000000 : ℝ)/8) ∧ Real.exp ((-133211267337/200000000000 : ℝ)/8) ≤ (920114608643222807/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133211267337/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0098_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098445483/20000000000 : ℝ) ≤ 4*Real.exp (251/2048 : ℝ)*Real.exp (-mu (radius 8 (2009/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (41098445483/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2009/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0098_exp_radius
  have hrNumeric : (984789413947/1000000000000 : ℝ) ≤ Real.exp (-2009/131072 : ℝ) ∧ Real.exp (-2009/131072 : ℝ) ≤ (246197353487/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984789413947/1000000000000 : ℝ) ≤ (radius 8 (2009/16384 : ℝ)) ∧ (radius 8 (2009/16384 : ℝ)) ≤ (246197353487/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2009/16384 : ℝ)) (984789413947/1000000000000 : ℝ) (246197353487/250000000000 : ℝ) (43438037893/250000000000 : ℝ) (86876075789/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2009/16384 : ℝ)) (984789413947/1000000000000 : ℝ) (246197353487/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2009/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984789413947/1000000000000 : ℝ) (246197353487/250000000000 : ℝ) (992394706973/1000000000000 : ℝ) (496197353487/500000000000 : ℝ) (3876427987/3906250000 : ℝ) (992365564673/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2009/16384 : ℝ)) 1 (992394706973/1000000000000 : ℝ) (496197353487/500000000000 : ℝ) (3876427987/3906250000 : ℝ) (992365564673/1000000000000 : ℝ) (496190067911/500000000000 : ℝ) (62023758489/62500000000 : ℝ) (198476027143/200000000000 : ℝ) (992380135717/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2009/16384 : ℝ)) 2 (496190067911/500000000000 : ℝ) (62023758489/62500000000 : ℝ) (198476027143/200000000000 : ℝ) (992380135717/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2009/16384 : ℝ)) 3 (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2009/16384 : ℝ)) 4 (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2009/16384 : ℝ)) 5 (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2009/16384 : ℝ)) 6 (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2009/16384 : ℝ)) 7 (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2009/16384 : ℝ))) (43438037893/250000000000 : ℝ) (86876075789/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2009/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43438037893/250000000000 : ℝ) (86876075789/500000000000 : ℝ) (293438037893/500000000000 : ℝ) (586876075789/1000000000000 : ℝ) (416835880859/1000000000000 : ℝ) (416835880867/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2009/16384 : ℝ))) 1 (293438037893/500000000000 : ℝ) (586876075789/1000000000000 : ℝ) (416835880859/1000000000000 : ℝ) (416835880867/1000000000000 : ℝ) (250927989161/500000000000 : ℝ) (62731997291/125000000000 : ℝ) (123650466539/250000000000 : ℝ) (494601866163/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2009/16384 : ℝ))) 2 (250927989161/500000000000 : ℝ) (62731997291/125000000000 : ℝ) (123650466539/250000000000 : ℝ) (494601866163/1000000000000 : ℝ) (498228922239/1000000000000 : ℝ) (249114461123/500000000000 : ℝ) (498215719763/1000000000000 : ℝ) (498215719771/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2009/16384 : ℝ))) 3 (498228922239/1000000000000 : ℝ) (249114461123/500000000000 : ℝ) (498215719763/1000000000000 : ℝ) (498215719771/1000000000000 : ℝ) (498222321001/1000000000000 : ℝ) (498222321009/1000000000000 : ℝ) (498222320957/1000000000000 : ℝ) (99644464193/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2009/16384 : ℝ))) 4 (498222321001/1000000000000 : ℝ) (498222321009/1000000000000 : ℝ) (498222320957/1000000000000 : ℝ) (99644464193/200000000000 : ℝ) (498222320979/1000000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2009/16384 : ℝ))) 5 (498222320979/1000000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2009/16384 : ℝ))) 6 (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2009/16384 : ℝ))) 7 (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2009/16384 : ℝ)) hmem 8 (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2009/16384 : ℝ))) hcmem 8 (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2009/16384 : ℝ)) (124047516971/125000000000 : ℝ) (992380135771/1000000000000 : ℝ) (249111160489/500000000000 : ℝ) (498222320987/1000000000000 : ℝ) (394307465209/500000000000 : ℝ) (157722986087/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0098_exp_lower
  have heNumeric : (41098445483/20000000000 : ℝ)/4 ≤ Real.exp (-133211267337/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098445483/20000000000 : ℝ)/4 ≤ Real.exp ((251/2048 : ℝ)-(157722986087/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (251/2048 : ℝ) (2009/16384 : ℝ) (157722986087/200000000000 : ℝ) (41098445483/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0099; no trusted numerical premise.
theorem cover8_leaf0099_exp_radius : (998084950675441671/1000000000000000000 : ℝ) ≤ Real.exp ((-1005/65536 : ℝ)/8) ∧ Real.exp ((-1005/65536 : ℝ)/8) ≤ (124760618834430209/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1005/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0099_exp_lower : (920114414920732049/1000000000000000000 : ℝ) ≤ Real.exp ((-106569283363/160000000000 : ℝ)/8) ∧ Real.exp ((-106569283363/160000000000 : ℝ)/8) ≤ (18402288298414641/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-106569283363/160000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0099_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027459406489/500000000000 : ℝ) ≤ 4*Real.exp (2009/16384 : ℝ)*Real.exp (-mu (radius 8 (1005/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027459406489/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1005/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0099_exp_radius
  have hrNumeric : (984781900629/1000000000000 : ℝ) ≤ Real.exp (-1005/65536 : ℝ) ∧ Real.exp (-1005/65536 : ℝ) ≤ (98478190063/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984781900629/1000000000000 : ℝ) ≤ (radius 8 (1005/8192 : ℝ)) ∧ (radius 8 (1005/8192 : ℝ)) ≤ (98478190063/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1005/8192 : ℝ)) (984781900629/1000000000000 : ℝ) (98478190063/100000000000 : ℝ) (34758946009/200000000000 : ℝ) (43448682513/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1005/8192 : ℝ)) (984781900629/1000000000000 : ℝ) (98478190063/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1005/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984781900629/1000000000000 : ℝ) (98478190063/100000000000 : ℝ) (496195475157/500000000000 : ℝ) (198478190063/200000000000 : ℝ) (198472355821/200000000000 : ℝ) (496180889553/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1005/8192 : ℝ)) 1 (496195475157/500000000000 : ℝ) (198478190063/200000000000 : ℝ) (198472355821/200000000000 : ℝ) (496180889553/500000000000 : ℝ) (992376364709/1000000000000 : ℝ) (992376364711/1000000000000 : ℝ) (496188182301/500000000000 : ℝ) (248094091151/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1005/8192 : ℝ)) 2 (992376364709/1000000000000 : ℝ) (992376364711/1000000000000 : ℝ) (496188182301/500000000000 : ℝ) (248094091151/250000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1005/8192 : ℝ)) 3 (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1005/8192 : ℝ)) 4 (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1005/8192 : ℝ)) 5 (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1005/8192 : ℝ)) 6 (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1005/8192 : ℝ)) 7 (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1005/8192 : ℝ))) (34758946009/200000000000 : ℝ) (43448682513/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1005/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (34758946009/200000000000 : ℝ) (43448682513/250000000000 : ℝ) (293448682511/500000000000 : ℝ) (293448682513/500000000000 : ℝ) (416886951157/1000000000000 : ℝ) (208443475583/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1005/8192 : ℝ))) 1 (293448682511/500000000000 : ℝ) (293448682513/500000000000 : ℝ) (416886951157/1000000000000 : ℝ) (208443475583/500000000000 : ℝ) (501892158089/1000000000000 : ℝ) (31368259881/62500000000 : ℝ) (494641135719/1000000000000 : ℝ) (494641135727/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1005/8192 : ℝ))) 2 (501892158089/1000000000000 : ℝ) (31368259881/62500000000 : ℝ) (494641135719/1000000000000 : ℝ) (494641135727/1000000000000 : ℝ) (62283330863/125000000000 : ℝ) (3892708179/7812500000 : ℝ) (15570420521/31250000000 : ℝ) (12456336417/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1005/8192 : ℝ))) 3 (62283330863/125000000000 : ℝ) (3892708179/7812500000 : ℝ) (15570420521/31250000000 : ℝ) (12456336417/25000000000 : ℝ) (124565012947/250000000000 : ℝ) (124565012949/250000000000 : ℝ) (15570626617/31250000000 : ℝ) (498260051753/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1005/8192 : ℝ))) 4 (124565012947/250000000000 : ℝ) (124565012949/250000000000 : ℝ) (15570626617/31250000000 : ℝ) (498260051753/1000000000000 : ℝ) (249130025883/500000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1005/8192 : ℝ))) 5 (249130025883/500000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1005/8192 : ℝ))) 6 (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1005/8192 : ℝ))) 7 (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1005/8192 : ℝ)) hmem 8 (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1005/8192 : ℝ))) hcmem 8 (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1005/8192 : ℝ)) (198475272931/200000000000 : ℝ) (496188182329/500000000000 : ℝ) (99652010353/200000000000 : ℝ) (19930402071/40000000000 : ℝ) (394338824953/500000000000 : ℝ) (31547105997/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0099_exp_lower
  have heNumeric : (1027459406489/500000000000 : ℝ)/4 ≤ Real.exp (-106569283363/160000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027459406489/500000000000 : ℝ)/4 ≤ Real.exp ((2009/16384 : ℝ)-(31547105997/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2009/16384 : ℝ) (1005/8192 : ℝ) (31547105997/40000000000 : ℝ) (1027459406489/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0075_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0075_certificate
#check SmaleRate.Proofs.cover8_leaf0076_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0076_certificate
#check SmaleRate.Proofs.cover8_leaf0077_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0077_certificate
#check SmaleRate.Proofs.cover8_leaf0078_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0078_certificate
#check SmaleRate.Proofs.cover8_leaf0079_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0079_certificate
#check SmaleRate.Proofs.cover8_leaf0080_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0080_certificate
#check SmaleRate.Proofs.cover8_leaf0081_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0081_certificate
#check SmaleRate.Proofs.cover8_leaf0082_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0082_certificate
#check SmaleRate.Proofs.cover8_leaf0083_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0083_certificate
#check SmaleRate.Proofs.cover8_leaf0084_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0084_certificate
#check SmaleRate.Proofs.cover8_leaf0085_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0085_certificate
#check SmaleRate.Proofs.cover8_leaf0086_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0086_certificate
#check SmaleRate.Proofs.cover8_leaf0087_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0087_certificate
#check SmaleRate.Proofs.cover8_leaf0088_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0088_certificate
#check SmaleRate.Proofs.cover8_leaf0089_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0089_certificate
#check SmaleRate.Proofs.cover8_leaf0090_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0090_certificate
#check SmaleRate.Proofs.cover8_leaf0091_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0091_certificate
#check SmaleRate.Proofs.cover8_leaf0092_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0092_certificate
#check SmaleRate.Proofs.cover8_leaf0093_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0093_certificate
#check SmaleRate.Proofs.cover8_leaf0094_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0094_certificate
#check SmaleRate.Proofs.cover8_leaf0095_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0095_certificate
#check SmaleRate.Proofs.cover8_leaf0096_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0096_certificate
#check SmaleRate.Proofs.cover8_leaf0097_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0097_certificate
#check SmaleRate.Proofs.cover8_leaf0098_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0098_certificate
#check SmaleRate.Proofs.cover8_leaf0099_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0099_certificate
