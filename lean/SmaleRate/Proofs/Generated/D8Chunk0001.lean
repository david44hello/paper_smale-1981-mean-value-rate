/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0025; no trusted numerical premise.
theorem cover8_leaf0025_exp_radius : (998269626267302513/1000000000000000000 : ℝ) ≤ Real.exp ((-227/16384 : ℝ)/8) ∧ Real.exp ((-227/16384 : ℝ)/8) ≤ (499134813133651257/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-227/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0025_exp_lower : (920151345353157507/1000000000000000000 : ℝ) ≤ Real.exp ((-1664342333/2500000000 : ℝ)/8) ∧ Real.exp ((-1664342333/2500000000 : ℝ)/8) ≤ (230037836338289377/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1664342333/2500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0025_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055578728317/1000000000000 : ℝ) ≤ 4*Real.exp (113/1024 : ℝ)*Real.exp (-mu (radius 8 (227/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055578728317/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (227/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0025_exp_radius
  have hrNumeric : (246560139509/250000000000 : ℝ) ≤ Real.exp (-227/16384 : ℝ) ∧ Real.exp (-227/16384 : ℝ) ≤ (986240558037/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246560139509/250000000000 : ℝ) ≤ (radius 8 (227/2048 : ℝ)) ∧ (radius 8 (227/2048 : ℝ)) ≤ (986240558037/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (227/2048 : ℝ)) (246560139509/250000000000 : ℝ) (986240558037/1000000000000 : ℝ) (10332284371/62500000000 : ℝ) (165316549943/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (227/2048 : ℝ)) (246560139509/250000000000 : ℝ) (986240558037/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (227/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246560139509/250000000000 : ℝ) (986240558037/1000000000000 : ℝ) (496560139509/500000000000 : ℝ) (993120279019/1000000000000 : ℝ) (993096449513/1000000000000 : ℝ) (496548224757/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (227/2048 : ℝ)) 1 (496560139509/500000000000 : ℝ) (993120279019/1000000000000 : ℝ) (993096449513/1000000000000 : ℝ) (496548224757/500000000000 : ℝ) (198621672853/200000000000 : ℝ) (993108364267/1000000000000 : ℝ) (496554182097/500000000000 : ℝ) (248277091049/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (227/2048 : ℝ)) 2 (198621672853/200000000000 : ℝ) (993108364267/1000000000000 : ℝ) (496554182097/500000000000 : ℝ) (248277091049/250000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (227/2048 : ℝ)) 3 (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (227/2048 : ℝ)) 4 (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (227/2048 : ℝ)) 5 (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (227/2048 : ℝ)) 6 (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (227/2048 : ℝ)) 7 (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (227/2048 : ℝ))) (10332284371/62500000000 : ℝ) (165316549943/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (227/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (10332284371/62500000000 : ℝ) (165316549943/1000000000000 : ℝ) (72832284371/125000000000 : ℝ) (145664568743/250000000000 : ℝ) (101647844891/250000000000 : ℝ) (406591379573/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (227/2048 : ℝ))) 1 (72832284371/125000000000 : ℝ) (145664568743/250000000000 : ℝ) (101647844891/250000000000 : ℝ) (406591379573/1000000000000 : ℝ) (247312413633/500000000000 : ℝ) (494624827273/1000000000000 : ℝ) (486727677283/1000000000000 : ℝ) (486727677291/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (227/2048 : ℝ))) 2 (247312413633/500000000000 : ℝ) (494624827273/1000000000000 : ℝ) (486727677283/1000000000000 : ℝ) (486727677291/1000000000000 : ℝ) (245338126137/500000000000 : ℝ) (245338126141/500000000000 : ℝ) (49066036451/100000000000 : ℝ) (490660364519/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (227/2048 : ℝ))) 3 (245338126137/500000000000 : ℝ) (245338126141/500000000000 : ℝ) (49066036451/100000000000 : ℝ) (490660364519/1000000000000 : ℝ) (61333538549/125000000000 : ℝ) (490668308401/1000000000000 : ℝ) (490668308327/1000000000000 : ℝ) (490668308337/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (227/2048 : ℝ))) 4 (61333538549/125000000000 : ℝ) (490668308401/1000000000000 : ℝ) (490668308327/1000000000000 : ℝ) (490668308337/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (227/2048 : ℝ))) 5 (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (227/2048 : ℝ))) 6 (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (227/2048 : ℝ))) 7 (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (227/2048 : ℝ)) hmem 8 (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (227/2048 : ℝ))) hcmem 8 (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (227/2048 : ℝ)) (993108364229/1000000000000 : ℝ) (124138545529/125000000000 : ℝ) (490668308359/1000000000000 : ℝ) (490668308369/1000000000000 : ℝ) (2425276549/3125000000 : ℝ) (7760884957/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0025_exp_lower
  have heNumeric : (2055578728317/1000000000000 : ℝ)/4 ≤ Real.exp (-1664342333/2500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055578728317/1000000000000 : ℝ)/4 ≤ Real.exp ((113/1024 : ℝ)-(7760884957/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (113/1024 : ℝ) (227/2048 : ℝ) (7760884957/10000000000 : ℝ) (2055578728317/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0026; no trusted numerical premise.
theorem cover8_leaf0026_exp_radius : (124782751262941069/125000000000000000 : ℝ) ≤ Real.exp ((-57/4096 : ℝ)/8) ∧ Real.exp ((-57/4096 : ℝ)/8) ≤ (998262010103528553/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-57/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0026_exp_lower : (460072878390679807/500000000000000000 : ℝ) ≤ Real.exp ((-665785521631/1000000000000 : ℝ)/8) ∧ Real.exp ((-665785521631/1000000000000 : ℝ)/8) ≤ (184029151356271923/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665785521631/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0026_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027739426699/500000000000 : ℝ) ≤ 4*Real.exp (227/2048 : ℝ)*Real.exp (-mu (radius 8 (57/512 : ℝ))) ∧ (20549/10000 : ℝ) < (1027739426699/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (57/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0026_exp_radius
  have hrNumeric : (493090182263/500000000000 : ℝ) ≤ Real.exp (-57/4096 : ℝ) ∧ Real.exp (-57/4096 : ℝ) ≤ (986180364527/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (493090182263/500000000000 : ℝ) ≤ (radius 8 (57/512 : ℝ)) ∧ (radius 8 (57/512 : ℝ)) ≤ (986180364527/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (57/512 : ℝ)) (493090182263/500000000000 : ℝ) (986180364527/1000000000000 : ℝ) (165675250479/1000000000000 : ℝ) (82837625243/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (57/512 : ℝ)) (493090182263/500000000000 : ℝ) (986180364527/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (57/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (493090182263/500000000000 : ℝ) (986180364527/1000000000000 : ℝ) (993090182263/1000000000000 : ℝ) (124136272783/125000000000 : ℝ) (993066143077/1000000000000 : ℝ) (496533071539/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (57/512 : ℝ)) 1 (993090182263/1000000000000 : ℝ) (124136272783/125000000000 : ℝ) (993066143077/1000000000000 : ℝ) (496533071539/500000000000 : ℝ) (99307816267/100000000000 : ℝ) (993078162671/1000000000000 : ℝ) (993078162597/1000000000000 : ℝ) (993078162599/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (57/512 : ℝ)) 2 (99307816267/100000000000 : ℝ) (993078162671/1000000000000 : ℝ) (993078162597/1000000000000 : ℝ) (993078162599/1000000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (57/512 : ℝ)) 3 (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (57/512 : ℝ)) 4 (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (57/512 : ℝ)) 5 (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (57/512 : ℝ)) 6 (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (57/512 : ℝ)) 7 (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (57/512 : ℝ))) (165675250479/1000000000000 : ℝ) (82837625243/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (57/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (165675250479/1000000000000 : ℝ) (82837625243/500000000000 : ℝ) (582837625239/1000000000000 : ℝ) (582837625243/1000000000000 : ℝ) (101758061867/250000000000 : ℝ) (407032247477/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (57/512 : ℝ))) 1 (582837625239/1000000000000 : ℝ) (582837625243/1000000000000 : ℝ) (101758061867/250000000000 : ℝ) (407032247477/1000000000000 : ℝ) (494934936353/1000000000000 : ℝ) (12373373409/25000000000 : ℝ) (48706643131/100000000000 : ℝ) (243533215659/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (57/512 : ℝ))) 2 (494934936353/1000000000000 : ℝ) (12373373409/25000000000 : ℝ) (48706643131/100000000000 : ℝ) (243533215659/500000000000 : ℝ) (491000683831/1000000000000 : ℝ) (491000683839/1000000000000 : ℝ) (24549246077/50000000000 : ℝ) (122746230387/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (57/512 : ℝ))) 3 (491000683831/1000000000000 : ℝ) (491000683839/1000000000000 : ℝ) (24549246077/50000000000 : ℝ) (122746230387/250000000000 : ℝ) (98198560537/200000000000 : ℝ) (245496401347/500000000000 : ℝ) (245496401311/500000000000 : ℝ) (490992802631/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (57/512 : ℝ))) 4 (98198560537/200000000000 : ℝ) (245496401347/500000000000 : ℝ) (245496401311/500000000000 : ℝ) (490992802631/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (57/512 : ℝ))) 5 (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (57/512 : ℝ))) 6 (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (57/512 : ℝ))) 7 (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (57/512 : ℝ)) hmem 8 (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (57/512 : ℝ))) hcmem 8 (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (57/512 : ℝ)) (993078162633/1000000000000 : ℝ) (198615632527/200000000000 : ℝ) (490992802653/1000000000000 : ℝ) (490992802663/1000000000000 : ℝ) (388312682681/500000000000 : ℝ) (776625365381/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0026_exp_lower
  have heNumeric : (1027739426699/500000000000 : ℝ)/4 ≤ Real.exp (-665785521631/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027739426699/500000000000 : ℝ)/4 ≤ Real.exp ((227/2048 : ℝ)-(776625365381/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (227/2048 : ℝ) (57/512 : ℝ) (776625365381/1000000000000 : ℝ) (1027739426699/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0027; no trusted numerical premise.
theorem cover8_leaf0027_exp_radius : (31195449812433159/31250000000000000 : ℝ) ≤ Real.exp ((-229/16384 : ℝ)/8) ∧ Real.exp ((-229/16384 : ℝ)/8) ≤ (998254393997861089/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-229/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0027_exp_lower : (184028070711306433/200000000000000000 : ℝ) ≤ Real.exp ((-66583249889/100000000000 : ℝ)/8) ∧ Real.exp ((-66583249889/100000000000 : ℝ)/8) ≤ (460070176778266083/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66583249889/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0027_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055382294903/1000000000000 : ℝ) ≤ 4*Real.exp (57/512 : ℝ)*Real.exp (-mu (radius 8 (229/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055382294903/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (229/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0027_exp_radius
  have hrNumeric : (98612017469/100000000000 : ℝ) ≤ Real.exp (-229/16384 : ℝ) ∧ Real.exp (-229/16384 : ℝ) ≤ (986120174691/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98612017469/100000000000 : ℝ) ≤ (radius 8 (229/2048 : ℝ)) ∧ (radius 8 (229/2048 : ℝ)) ≤ (986120174691/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (229/2048 : ℝ)) (98612017469/100000000000 : ℝ) (986120174691/1000000000000 : ℝ) (83016566219/500000000000 : ℝ) (33206626489/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (229/2048 : ℝ)) (98612017469/100000000000 : ℝ) (986120174691/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (229/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98612017469/100000000000 : ℝ) (986120174691/1000000000000 : ℝ) (198612017469/200000000000 : ℝ) (496530043673/500000000000 : ℝ) (198607167513/200000000000 : ℝ) (993035837567/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (229/2048 : ℝ)) 1 (198612017469/200000000000 : ℝ) (496530043673/500000000000 : ℝ) (198607167513/200000000000 : ℝ) (993035837567/1000000000000 : ℝ) (198609592491/200000000000 : ℝ) (993047962457/1000000000000 : ℝ) (49652398119/50000000000 : ℝ) (993047962383/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (229/2048 : ℝ)) 2 (198609592491/200000000000 : ℝ) (993047962457/1000000000000 : ℝ) (49652398119/50000000000 : ℝ) (993047962383/1000000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (229/2048 : ℝ)) 3 (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (229/2048 : ℝ)) 4 (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (229/2048 : ℝ)) 5 (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (229/2048 : ℝ)) 6 (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (229/2048 : ℝ)) 7 (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (229/2048 : ℝ))) (83016566219/500000000000 : ℝ) (33206626489/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (229/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (83016566219/500000000000 : ℝ) (33206626489/200000000000 : ℝ) (583016566219/1000000000000 : ℝ) (583016566223/1000000000000 : ℝ) (81494326781/200000000000 : ℝ) (81494326783/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (229/2048 : ℝ))) 1 (583016566219/1000000000000 : ℝ) (583016566223/1000000000000 : ℝ) (81494326781/200000000000 : ℝ) (81494326783/200000000000 : ℝ) (247622050031/500000000000 : ℝ) (495244100069/1000000000000 : ℝ) (97480811/200000000 : ℝ) (487404055009/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (229/2048 : ℝ))) 2 (247622050031/500000000000 : ℝ) (495244100069/1000000000000 : ℝ) (97480811/200000000 : ℝ) (487404055009/1000000000000 : ℝ) (491324077531/1000000000000 : ℝ) (491324077539/1000000000000 : ℝ) (245654219679/500000000000 : ℝ) (491308439367/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (229/2048 : ℝ))) 3 (491324077531/1000000000000 : ℝ) (491324077539/1000000000000 : ℝ) (245654219679/500000000000 : ℝ) (491308439367/1000000000000 : ℝ) (122829064611/250000000000 : ℝ) (491316258453/1000000000000 : ℝ) (245658129191/500000000000 : ℝ) (491316258391/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (229/2048 : ℝ))) 4 (122829064611/250000000000 : ℝ) (491316258453/1000000000000 : ℝ) (245658129191/500000000000 : ℝ) (491316258391/1000000000000 : ℝ) (491316258413/1000000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (229/2048 : ℝ))) 5 (491316258413/1000000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (229/2048 : ℝ))) 6 (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (229/2048 : ℝ))) 7 (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (229/2048 : ℝ)) hmem 8 (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (229/2048 : ℝ))) hcmem 8 (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (229/2048 : ℝ)) (993047962417/1000000000000 : ℝ) (49652398121/50000000000 : ℝ) (122829064603/250000000000 : ℝ) (245658129211/500000000000 : ℝ) (777160623871/1000000000000 : ℝ) (77716062389/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0027_exp_lower
  have heNumeric : (2055382294903/1000000000000 : ℝ)/4 ≤ Real.exp (-66583249889/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055382294903/1000000000000 : ℝ)/4 ≤ Real.exp ((57/512 : ℝ)-(77716062389/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (57/512 : ℝ) (229/2048 : ℝ) (77716062389/100000000000 : ℝ) (2055382294903/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0028; no trusted numerical premise.
theorem cover8_leaf0028_exp_radius : (998246777950299677/1000000000000000000 : ℝ) ≤ Real.exp ((-115/8192 : ℝ)/8) ∧ Real.exp ((-115/8192 : ℝ)/8) ≤ (499123388975149839/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-115/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0028_exp_lower : (460067567127820943/500000000000000000 : ℝ) ≤ Real.exp ((-665877877321/1000000000000 : ℝ)/8) ∧ Real.exp ((-665877877321/1000000000000 : ℝ)/8) ≤ (920135134255641887/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665877877321/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0028_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513822256749/250000000000 : ℝ) ≤ 4*Real.exp (229/2048 : ℝ)*Real.exp (-mu (radius 8 (115/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (513822256749/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (115/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0028_exp_radius
  have hrNumeric : (61628749283/62500000000 : ℝ) ≤ Real.exp (-115/8192 : ℝ) ∧ Real.exp (-115/8192 : ℝ) ≤ (986059988529/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61628749283/62500000000 : ℝ) ≤ (radius 8 (115/1024 : ℝ)) ∧ (radius 8 (115/1024 : ℝ)) ≤ (986059988529/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (115/1024 : ℝ)) (61628749283/62500000000 : ℝ) (986059988529/1000000000000 : ℝ) (1663902011/10000000000 : ℝ) (166390201107/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (115/1024 : ℝ)) (61628749283/62500000000 : ℝ) (986059988529/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (115/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61628749283/62500000000 : ℝ) (986059988529/1000000000000 : ℝ) (124128749283/125000000000 : ℝ) (198605998853/200000000000 : ℝ) (993005532979/1000000000000 : ℝ) (993005532981/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (115/1024 : ℝ)) 1 (124128749283/125000000000 : ℝ) (198605998853/200000000000 : ℝ) (993005532979/1000000000000 : ℝ) (993005532981/1000000000000 : ℝ) (993017763621/1000000000000 : ℝ) (993017763623/1000000000000 : ℝ) (496508881773/500000000000 : ℝ) (248254440887/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (115/1024 : ℝ)) 2 (993017763621/1000000000000 : ℝ) (993017763623/1000000000000 : ℝ) (496508881773/500000000000 : ℝ) (248254440887/250000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (115/1024 : ℝ)) 3 (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (115/1024 : ℝ)) 4 (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (115/1024 : ℝ)) 5 (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (115/1024 : ℝ)) 6 (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (115/1024 : ℝ)) 7 (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (115/1024 : ℝ))) (1663902011/10000000000 : ℝ) (166390201107/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (115/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1663902011/10000000000 : ℝ) (166390201107/1000000000000 : ℝ) (11663902011/20000000000 : ℝ) (291597550277/500000000000 : ℝ) (81581910029/200000000000 : ℝ) (81581910031/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (115/1024 : ℝ))) 1 (11663902011/20000000000 : ℝ) (291597550277/500000000000 : ℝ) (81581910029/200000000000 : ℝ) (81581910031/200000000000 : ℝ) (495552325347/1000000000000 : ℝ) (99110465071/200000000000 : ℝ) (487740557173/1000000000000 : ℝ) (243870278591/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (115/1024 : ℝ))) 2 (495552325347/1000000000000 : ℝ) (99110465071/200000000000 : ℝ) (487740557173/1000000000000 : ℝ) (243870278591/500000000000 : ℝ) (24582322063/50000000000 : ℝ) (491646441269/1000000000000 : ℝ) (491630925871/1000000000000 : ℝ) (12290773147/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (115/1024 : ℝ))) 3 (24582322063/50000000000 : ℝ) (491646441269/1000000000000 : ℝ) (491630925871/1000000000000 : ℝ) (12290773147/25000000000 : ℝ) (98327736713/200000000000 : ℝ) (19665547343/40000000000 : ℝ) (30727417719/62500000000 : ℝ) (245819341757/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (115/1024 : ℝ))) 4 (98327736713/200000000000 : ℝ) (19665547343/40000000000 : ℝ) (30727417719/62500000000 : ℝ) (245819341757/500000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (115/1024 : ℝ))) 5 (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (115/1024 : ℝ))) 6 (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (115/1024 : ℝ))) 7 (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (115/1024 : ℝ)) hmem 8 (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (115/1024 : ℝ))) hcmem 8 (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (115/1024 : ℝ)) (993017763583/1000000000000 : ℝ) (496508881793/500000000000 : ℝ) (245819341767/500000000000 : ℝ) (98327736709/200000000000 : ℝ) (777694283551/1000000000000 : ℝ) (777694283571/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0028_exp_lower
  have heNumeric : (513822256749/250000000000 : ℝ)/4 ≤ Real.exp (-665877877321/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513822256749/250000000000 : ℝ)/4 ≤ Real.exp ((229/2048 : ℝ)-(777694283571/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (229/2048 : ℝ) (115/1024 : ℝ) (777694283571/1000000000000 : ℝ) (513822256749/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0029; no trusted numerical premise.
theorem cover8_leaf0029_exp_radius : (249559790490210969/250000000000000000 : ℝ) ≤ Real.exp ((-231/16384 : ℝ)/8) ∧ Real.exp ((-231/16384 : ℝ)/8) ≤ (998239161960843877/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-231/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0029_exp_lower : (460065048736352987/500000000000000000 : ℝ) ≤ Real.exp ((-665921669121/1000000000000 : ℝ)/8) ∧ Real.exp ((-665921669121/1000000000000 : ℝ)/8) ≤ (36805203898908239/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665921669121/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0029_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055199024161/1000000000000 : ℝ) ≤ 4*Real.exp (115/1024 : ℝ)*Real.exp (-mu (radius 8 (231/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055199024161/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (231/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0029_exp_radius
  have hrNumeric : (985999806039/1000000000000 : ℝ) ≤ Real.exp (-231/16384 : ℝ) ∧ Real.exp (-231/16384 : ℝ) ≤ (24649995151/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985999806039/1000000000000 : ℝ) ≤ (radius 8 (231/2048 : ℝ)) ∧ (radius 8 (231/2048 : ℝ)) ≤ (24649995151/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (231/2048 : ℝ)) (985999806039/1000000000000 : ℝ) (24649995151/25000000000 : ℝ) (83373230849/500000000000 : ℝ) (33349292341/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (231/2048 : ℝ)) (985999806039/1000000000000 : ℝ) (24649995151/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (231/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985999806039/1000000000000 : ℝ) (24649995151/25000000000 : ℝ) (992999903019/1000000000000 : ℝ) (49649995151/50000000000 : ℝ) (992975229317/1000000000000 : ℝ) (992975229319/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (231/2048 : ℝ)) 1 (992999903019/1000000000000 : ℝ) (49649995151/50000000000 : ℝ) (992975229317/1000000000000 : ℝ) (992975229319/1000000000000 : ℝ) (124123445771/125000000000 : ℝ) (99298756617/100000000000 : ℝ) (992987566091/1000000000000 : ℝ) (992987566093/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (231/2048 : ℝ)) 2 (124123445771/125000000000 : ℝ) (99298756617/100000000000 : ℝ) (992987566091/1000000000000 : ℝ) (992987566093/1000000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (231/2048 : ℝ)) 3 (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (231/2048 : ℝ)) 4 (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (231/2048 : ℝ)) 5 (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (231/2048 : ℝ)) 6 (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (231/2048 : ℝ)) 7 (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (231/2048 : ℝ))) (83373230849/500000000000 : ℝ) (33349292341/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (231/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (83373230849/500000000000 : ℝ) (33349292341/200000000000 : ℝ) (583373230849/1000000000000 : ℝ) (583373230853/1000000000000 : ℝ) (102086501831/250000000000 : ℝ) (204173003667/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (231/2048 : ℝ))) 1 (583373230849/1000000000000 : ℝ) (583373230853/1000000000000 : ℝ) (102086501831/250000000000 : ℝ) (204173003667/500000000000 : ℝ) (247929809543/500000000000 : ℝ) (247929809547/500000000000 : ℝ) (244037973273/500000000000 : ℝ) (244037973277/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (231/2048 : ℝ))) 2 (247929809543/500000000000 : ℝ) (247929809547/500000000000 : ℝ) (244037973273/500000000000 : ℝ) (244037973277/500000000000 : ℝ) (15373993213/31250000000 : ℝ) (61495972853/125000000000 : ℝ) (245976194447/500000000000 : ℝ) (491952388903/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (231/2048 : ℝ))) 3 (15373993213/31250000000 : ℝ) (61495972853/125000000000 : ℝ) (245976194447/500000000000 : ℝ) (491952388903/1000000000000 : ℝ) (98392017171/200000000000 : ℝ) (61495010733/125000000000 : ℝ) (245980042897/500000000000 : ℝ) (122990021451/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (231/2048 : ℝ))) 4 (98392017171/200000000000 : ℝ) (61495010733/125000000000 : ℝ) (245980042897/500000000000 : ℝ) (122990021451/250000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (231/2048 : ℝ))) 5 (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (231/2048 : ℝ))) 6 (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (231/2048 : ℝ))) 7 (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (231/2048 : ℝ)) hmem 8 (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (231/2048 : ℝ))) hcmem 8 (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (231/2048 : ℝ)) (992987566129/1000000000000 : ℝ) (248246891533/250000000000 : ℝ) (7686876341/15625000000 : ℝ) (245980042917/500000000000 : ℝ) (389113178301/500000000000 : ℝ) (778226356621/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0029_exp_lower
  have heNumeric : (2055199024161/1000000000000 : ℝ)/4 ≤ Real.exp (-665921669121/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055199024161/1000000000000 : ℝ)/4 ≤ Real.exp ((115/1024 : ℝ)-(778226356621/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (115/1024 : ℝ) (231/2048 : ℝ) (778226356621/1000000000000 : ℝ) (2055199024161/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0030; no trusted numerical premise.
theorem cover8_leaf0030_exp_radius : (499115773014746621/500000000000000000 : ℝ) ≤ Real.exp ((-29/2048 : ℝ)/8) ∧ Real.exp ((-29/2048 : ℝ)/8) ≤ (998231546029493243/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-29/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0030_exp_lower : (920125241819363889/1000000000000000000 : ℝ) ≤ Real.exp ((-133192777267/200000000000 : ℝ)/8) ∧ Real.exp ((-133192777267/200000000000 : ℝ)/8) ≤ (92012524181936389/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133192777267/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0030_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (411022452243/200000000000 : ℝ) ≤ 4*Real.exp (231/2048 : ℝ)*Real.exp (-mu (radius 8 (29/256 : ℝ))) ∧ (20549/10000 : ℝ) < (411022452243/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (29/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0030_exp_radius
  have hrNumeric : (123242453403/125000000000 : ℝ) ≤ Real.exp (-29/2048 : ℝ) ∧ Real.exp (-29/2048 : ℝ) ≤ (39437585089/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123242453403/125000000000 : ℝ) ≤ (radius 8 (29/256 : ℝ)) ∧ (radius 8 (29/256 : ℝ)) ≤ (39437585089/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (29/256 : ℝ)) (123242453403/125000000000 : ℝ) (39437585089/40000000000 : ℝ) (835509597/5000000000 : ℝ) (167101919407/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (29/256 : ℝ)) (123242453403/125000000000 : ℝ) (39437585089/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (29/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123242453403/125000000000 : ℝ) (39437585089/40000000000 : ℝ) (248242453403/250000000000 : ℝ) (992969813613/1000000000000 : ℝ) (992944926581/1000000000000 : ℝ) (992944926583/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (29/256 : ℝ)) 1 (248242453403/250000000000 : ℝ) (992969813613/1000000000000 : ℝ) (992944926581/1000000000000 : ℝ) (992944926583/1000000000000 : ℝ) (62059835631/62500000000 : ℝ) (496478685049/500000000000 : ℝ) (496478685009/500000000000 : ℝ) (992957370021/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (29/256 : ℝ)) 2 (62059835631/62500000000 : ℝ) (496478685049/500000000000 : ℝ) (496478685009/500000000000 : ℝ) (992957370021/1000000000000 : ℝ) (992957370057/1000000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (29/256 : ℝ)) 3 (992957370057/1000000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (29/256 : ℝ)) 4 (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (29/256 : ℝ)) 5 (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (29/256 : ℝ)) 6 (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (29/256 : ℝ)) 7 (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (29/256 : ℝ))) (835509597/5000000000 : ℝ) (167101919407/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (29/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (835509597/5000000000 : ℝ) (167101919407/1000000000000 : ℝ) (5835509597/10000000000 : ℝ) (72943869963/125000000000 : ℝ) (408781016437/1000000000000 : ℝ) (408781016447/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (29/256 : ℝ))) 1 (5835509597/10000000000 : ℝ) (72943869963/125000000000 : ℝ) (408781016437/1000000000000 : ℝ) (408781016447/1000000000000 : ℝ) (124041497017/250000000000 : ℝ) (124041497019/250000000000 : ℝ) (12210255793/25000000000 : ℝ) (30525639483/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (29/256 : ℝ))) 2 (124041497017/250000000000 : ℝ) (124041497019/250000000000 : ℝ) (12210255793/25000000000 : ℝ) (30525639483/62500000000 : ℝ) (246144054947/500000000000 : ℝ) (246144054951/500000000000 : ℝ) (246136418071/500000000000 : ℝ) (492272836151/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (29/256 : ℝ))) 3 (246144054947/500000000000 : ℝ) (246144054951/500000000000 : ℝ) (246136418071/500000000000 : ℝ) (492272836151/1000000000000 : ℝ) (246140236509/500000000000 : ℝ) (492280473027/1000000000000 : ℝ) (246140236479/500000000000 : ℝ) (61535059121/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (29/256 : ℝ))) 4 (246140236509/500000000000 : ℝ) (492280473027/1000000000000 : ℝ) (246140236479/500000000000 : ℝ) (61535059121/125000000000 : ℝ) (123070118247/250000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (29/256 : ℝ))) 5 (123070118247/250000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (29/256 : ℝ))) 6 (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (29/256 : ℝ))) 7 (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (29/256 : ℝ)) hmem 8 (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (29/256 : ℝ))) hcmem 8 (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (29/256 : ℝ)) (124119671257/125000000000 : ℝ) (49647868503/50000000000 : ℝ) (492280472987/1000000000000 : ℝ) (246140236499/500000000000 : ℝ) (97344606883/125000000000 : ℝ) (155751371017/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0030_exp_lower
  have heNumeric : (411022452243/200000000000 : ℝ)/4 ≤ Real.exp (-133192777267/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (411022452243/200000000000 : ℝ)/4 ≤ Real.exp ((231/2048 : ℝ)-(155751371017/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (231/2048 : ℝ) (29/256 : ℝ) (155751371017/200000000000 : ℝ) (411022452243/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0031; no trusted numerical premise.
theorem cover8_leaf0031_exp_radius : (998223930156247331/1000000000000000000 : ℝ) ≤ Real.exp ((-233/16384 : ℝ)/8) ∧ Real.exp ((-233/16384 : ℝ)/8) ≤ (249555982539061833/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-233/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0031_exp_lower : (920120565921883751/1000000000000000000 : ℝ) ≤ Real.exp ((-333002270441/500000000000 : ℝ)/8) ∧ Real.exp ((-333002270441/500000000000 : ℝ)/8) ≤ (115015070740235469/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333002270441/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0031_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (411005742651/200000000000 : ℝ) ≤ 4*Real.exp (29/256 : ℝ)*Real.exp (-mu (radius 8 (233/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (411005742651/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (233/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0031_exp_radius
  have hrNumeric : (985879452081/1000000000000 : ℝ) ≤ Real.exp (-233/16384 : ℝ) ∧ Real.exp (-233/16384 : ℝ) ≤ (492939726041/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985879452081/1000000000000 : ℝ) ≤ (radius 8 (233/2048 : ℝ)) ∧ (radius 8 (233/2048 : ℝ)) ≤ (492939726041/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (233/2048 : ℝ)) (985879452081/1000000000000 : ℝ) (492939726041/500000000000 : ℝ) (83728289667/500000000000 : ℝ) (167456579341/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (233/2048 : ℝ)) (985879452081/1000000000000 : ℝ) (492939726041/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (233/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985879452081/1000000000000 : ℝ) (492939726041/500000000000 : ℝ) (24823493151/25000000000 : ℝ) (992939726041/1000000000000 : ℝ) (992914624769/1000000000000 : ℝ) (99291462477/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (233/2048 : ℝ)) 1 (24823493151/25000000000 : ℝ) (992939726041/1000000000000 : ℝ) (992914624769/1000000000000 : ℝ) (99291462477/100000000000 : ℝ) (248231793851/250000000000 : ℝ) (496463587703/500000000000 : ℝ) (39717087013/40000000000 : ℝ) (992927175327/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (233/2048 : ℝ)) 2 (248231793851/250000000000 : ℝ) (496463587703/500000000000 : ℝ) (39717087013/40000000000 : ℝ) (992927175327/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (233/2048 : ℝ)) 3 (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (233/2048 : ℝ)) 4 (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (233/2048 : ℝ)) 5 (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (233/2048 : ℝ)) 6 (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (233/2048 : ℝ)) 7 (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (233/2048 : ℝ))) (83728289667/500000000000 : ℝ) (167456579341/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (233/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (83728289667/500000000000 : ℝ) (167456579341/1000000000000 : ℝ) (583728289667/1000000000000 : ℝ) (583728289671/1000000000000 : ℝ) (25575911773/62500000000 : ℝ) (204607294189/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (233/2048 : ℝ))) 1 (583728289667/1000000000000 : ℝ) (583728289671/1000000000000 : ℝ) (25575911773/62500000000 : ℝ) (204607294189/500000000000 : ℝ) (496471439017/1000000000000 : ℝ) (19858857561/40000000000 : ℝ) (61092927651/125000000000 : ℝ) (488743421217/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (233/2048 : ℝ))) 2 (496471439017/1000000000000 : ℝ) (19858857561/40000000000 : ℝ) (61092927651/125000000000 : ℝ) (488743421217/1000000000000 : ℝ) (15393982191/31250000000 : ℝ) (492607430121/1000000000000 : ℝ) (492592275251/1000000000000 : ℝ) (24629613763/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (233/2048 : ℝ))) 3 (15393982191/31250000000 : ℝ) (492607430121/1000000000000 : ℝ) (492592275251/1000000000000 : ℝ) (24629613763/50000000000 : ℝ) (492599852681/1000000000000 : ℝ) (492599852691/1000000000000 : ℝ) (492599852623/1000000000000 : ℝ) (492599852633/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (233/2048 : ℝ))) 4 (492599852681/1000000000000 : ℝ) (492599852691/1000000000000 : ℝ) (492599852623/1000000000000 : ℝ) (492599852633/1000000000000 : ℝ) (123149963163/250000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (233/2048 : ℝ))) 5 (123149963163/250000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (233/2048 : ℝ))) 6 (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (233/2048 : ℝ))) 7 (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (233/2048 : ℝ)) hmem 8 (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (233/2048 : ℝ))) hcmem 8 (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (233/2048 : ℝ)) (248231793841/250000000000 : ℝ) (992927175367/1000000000000 : ℝ) (492599852651/1000000000000 : ℝ) (246299926331/500000000000 : ℝ) (779285790861/1000000000000 : ℝ) (389642895441/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0031_exp_lower
  have heNumeric : (411005742651/200000000000 : ℝ)/4 ≤ Real.exp (-333002270441/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (411005742651/200000000000 : ℝ)/4 ≤ Real.exp ((29/256 : ℝ)-(389642895441/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (29/256 : ℝ) (233/2048 : ℝ) (389642895441/500000000000 : ℝ) (411005742651/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0032; no trusted numerical premise.
theorem cover8_leaf0032_exp_radius : (9982163143411057/10000000000000000 : ℝ) ≤ Real.exp ((-117/8192 : ℝ)/8) ∧ Real.exp ((-117/8192 : ℝ)/8) ≤ (998216314341105701/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-117/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0032_exp_lower : (920116068425414799/1000000000000000000 : ℝ) ≤ Real.exp ((-333021822259/500000000000 : ℝ)/8) ∧ Real.exp ((-333021822259/500000000000 : ℝ)/8) ≤ (2300290171063537/2500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333021822259/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0032_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513737088933/250000000000 : ℝ) ≤ 4*Real.exp (233/2048 : ℝ)*Real.exp (-mu (radius 8 (117/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (513737088933/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (117/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0032_exp_radius
  have hrNumeric : (985819280611/1000000000000 : ℝ) ≤ Real.exp (-117/8192 : ℝ) ∧ Real.exp (-117/8192 : ℝ) ≤ (246454820153/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985819280611/1000000000000 : ℝ) ≤ (radius 8 (117/1024 : ℝ)) ∧ (radius 8 (117/1024 : ℝ)) ≤ (246454820153/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (117/1024 : ℝ)) (985819280611/1000000000000 : ℝ) (246454820153/250000000000 : ℝ) (41952611639/250000000000 : ℝ) (167810446563/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (117/1024 : ℝ)) (985819280611/1000000000000 : ℝ) (246454820153/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (117/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985819280611/1000000000000 : ℝ) (246454820153/250000000000 : ℝ) (198581928061/200000000000 : ℝ) (496454820153/500000000000 : ℝ) (496442161941/500000000000 : ℝ) (992884323883/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (117/1024 : ℝ)) 1 (198581928061/200000000000 : ℝ) (496454820153/500000000000 : ℝ) (496442161941/500000000000 : ℝ) (992884323883/1000000000000 : ℝ) (992896982093/1000000000000 : ℝ) (198579396419/200000000000 : ℝ) (248224245503/250000000000 : ℝ) (496448491007/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (117/1024 : ℝ)) 2 (992896982093/1000000000000 : ℝ) (198579396419/200000000000 : ℝ) (248224245503/250000000000 : ℝ) (496448491007/500000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (117/1024 : ℝ)) 3 (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (117/1024 : ℝ)) 4 (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (117/1024 : ℝ)) 5 (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (117/1024 : ℝ)) 6 (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (117/1024 : ℝ)) 7 (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (117/1024 : ℝ))) (41952611639/250000000000 : ℝ) (167810446563/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (117/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (41952611639/250000000000 : ℝ) (167810446563/1000000000000 : ℝ) (291952611639/500000000000 : ℝ) (291952611641/500000000000 : ℝ) (102411683463/250000000000 : ℝ) (204823366931/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (117/1024 : ℝ))) 1 (291952611639/500000000000 : ℝ) (291952611641/500000000000 : ℝ) (102411683463/250000000000 : ℝ) (204823366931/500000000000 : ℝ) (99355195713/200000000000 : ℝ) (124193994643/250000000000 : ℝ) (244537761703/500000000000 : ℝ) (244537761707/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (117/1024 : ℝ))) 2 (99355195713/200000000000 : ℝ) (124193994643/250000000000 : ℝ) (244537761703/500000000000 : ℝ) (244537761707/500000000000 : ℝ) (98585150197/200000000000 : ℝ) (492925750993/1000000000000 : ℝ) (61613839219/125000000000 : ℝ) (492910713761/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (117/1024 : ℝ))) 3 (98585150197/200000000000 : ℝ) (492925750993/1000000000000 : ℝ) (61613839219/125000000000 : ℝ) (492910713761/1000000000000 : ℝ) (30807389523/62500000000 : ℝ) (492918232377/1000000000000 : ℝ) (492918232311/1000000000000 : ℝ) (385092369/781250000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (117/1024 : ℝ))) 4 (30807389523/62500000000 : ℝ) (492918232377/1000000000000 : ℝ) (492918232311/1000000000000 : ℝ) (385092369/781250000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (117/1024 : ℝ))) 5 (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (117/1024 : ℝ))) 6 (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (117/1024 : ℝ))) 7 (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (117/1024 : ℝ)) hmem 8 (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (117/1024 : ℝ))) hcmem 8 (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (117/1024 : ℝ)) (248224245513/250000000000 : ℝ) (198579396411/200000000000 : ℝ) (492918232339/1000000000000 : ℝ) (492918232349/1000000000000 : ℝ) (779813175749/1000000000000 : ℝ) (97476646971/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0032_exp_lower
  have heNumeric : (513737088933/250000000000 : ℝ)/4 ≤ Real.exp (-333021822259/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513737088933/250000000000 : ℝ)/4 ≤ Real.exp ((233/2048 : ℝ)-(97476646971/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (233/2048 : ℝ) (117/1024 : ℝ) (97476646971/125000000000 : ℝ) (513737088933/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0033; no trusted numerical premise.
theorem cover8_leaf0033_exp_radius : (998212506455323851/1000000000000000000 : ℝ) ≤ Real.exp ((-469/32768 : ℝ)/8) ∧ Real.exp ((-469/32768 : ℝ)/8) ≤ (249553126613830963/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-469/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0033_exp_lower : (460070983116884901/500000000000000000 : ℝ) ≤ Real.exp ((-665818477761/1000000000000 : ℝ)/8) ∧ Real.exp ((-665818477761/1000000000000 : ℝ)/8) ≤ (920141966233769803/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665818477761/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0033_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027705556943/500000000000 : ℝ) ≤ 4*Real.exp (117/1024 : ℝ)*Real.exp (-mu (radius 8 (469/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027705556943/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (469/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0033_exp_radius
  have hrNumeric : (985789196253/1000000000000 : ℝ) ≤ Real.exp (-469/32768 : ℝ) ∧ Real.exp (-469/32768 : ℝ) ≤ (492894598127/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985789196253/1000000000000 : ℝ) ≤ (radius 8 (469/4096 : ℝ)) ∧ (radius 8 (469/4096 : ℝ)) ≤ (492894598127/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (469/4096 : ℝ)) (985789196253/1000000000000 : ℝ) (492894598127/500000000000 : ℝ) (16798708447/100000000000 : ℝ) (167987084477/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (469/4096 : ℝ)) (985789196253/1000000000000 : ℝ) (492894598127/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (469/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985789196253/1000000000000 : ℝ) (492894598127/500000000000 : ℝ) (496447299063/500000000000 : ℝ) (992894598127/1000000000000 : ℝ) (198573834757/200000000000 : ℝ) (496434586893/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (469/4096 : ℝ)) 1 (496447299063/500000000000 : ℝ) (992894598127/1000000000000 : ℝ) (198573834757/200000000000 : ℝ) (496434586893/500000000000 : ℝ) (198576377191/200000000000 : ℝ) (992881885957/1000000000000 : ℝ) (496440942937/500000000000 : ℝ) (248220471469/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (469/4096 : ℝ)) 2 (198576377191/200000000000 : ℝ) (992881885957/1000000000000 : ℝ) (496440942937/500000000000 : ℝ) (248220471469/250000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (469/4096 : ℝ)) 3 (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (469/4096 : ℝ)) 4 (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (469/4096 : ℝ)) 5 (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (469/4096 : ℝ)) 6 (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (469/4096 : ℝ)) 7 (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (469/4096 : ℝ))) (16798708447/100000000000 : ℝ) (167987084477/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (469/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (16798708447/100000000000 : ℝ) (167987084477/1000000000000 : ℝ) (116798708447/200000000000 : ℝ) (583993542239/1000000000000 : ℝ) (204931137501/500000000000 : ℝ) (409862275011/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (469/4096 : ℝ))) 1 (116798708447/200000000000 : ℝ) (583993542239/1000000000000 : ℝ) (204931137501/500000000000 : ℝ) (409862275011/1000000000000 : ℝ) (248463954309/500000000000 : ℝ) (3975423269/8000000000 : ℝ) (48924116937/100000000000 : ℝ) (244620584689/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (469/4096 : ℝ))) 2 (248463954309/500000000000 : ℝ) (3975423269/8000000000 : ℝ) (48924116937/100000000000 : ℝ) (244620584689/500000000000 : ℝ) (246542269497/500000000000 : ℝ) (246542269501/500000000000 : ℝ) (493069560107/1000000000000 : ℝ) (123267390029/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (469/4096 : ℝ))) 3 (246542269497/500000000000 : ℝ) (246542269501/500000000000 : ℝ) (493069560107/1000000000000 : ℝ) (123267390029/250000000000 : ℝ) (9861540991/20000000000 : ℝ) (493077049559/1000000000000 : ℝ) (493077049493/1000000000000 : ℝ) (493077049503/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (469/4096 : ℝ))) 4 (9861540991/20000000000 : ℝ) (493077049559/1000000000000 : ℝ) (493077049493/1000000000000 : ℝ) (493077049503/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (469/4096 : ℝ))) 5 (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (469/4096 : ℝ))) 6 (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (469/4096 : ℝ))) 7 (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (469/4096 : ℝ)) hmem 8 (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (469/4096 : ℝ))) hcmem 8 (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (469/4096 : ℝ)) (496440942957/500000000000 : ℝ) (992881885917/1000000000000 : ℝ) (493077049521/1000000000000 : ℝ) (493077049531/1000000000000 : ℝ) (780076290241/1000000000000 : ℝ) (780076290261/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0033_exp_lower
  have heNumeric : (1027705556943/500000000000 : ℝ)/4 ≤ Real.exp (-665818477761/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027705556943/500000000000 : ℝ)/4 ≤ Real.exp ((117/1024 : ℝ)-(780076290261/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (117/1024 : ℝ) (469/4096 : ℝ) (780076290261/1000000000000 : ℝ) (1027705556943/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0034; no trusted numerical premise.
theorem cover8_leaf0034_exp_radius : (499104349292033953/500000000000000000 : ℝ) ≤ Real.exp ((-235/16384 : ℝ)/8) ∧ Real.exp ((-235/16384 : ℝ)/8) ≤ (998208698584067907/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-235/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0034_exp_lower : (920139828000001497/1000000000000000000 : ℝ) ≤ Real.exp ((-665837068251/1000000000000 : ℝ)/8) ∧ Real.exp ((-665837068251/1000000000000 : ℝ)/8) ≤ (460069914000000749/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665837068251/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0034_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055372903141/1000000000000 : ℝ) ≤ 4*Real.exp (469/4096 : ℝ)*Real.exp (-mu (radius 8 (235/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055372903141/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (235/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0034_exp_radius
  have hrNumeric : (985759112813/1000000000000 : ℝ) ≤ Real.exp (-235/16384 : ℝ) ∧ Real.exp (-235/16384 : ℝ) ≤ (492879556407/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985759112813/1000000000000 : ℝ) ≤ (radius 8 (235/2048 : ℝ)) ∧ (radius 8 (235/2048 : ℝ)) ≤ (492879556407/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (235/2048 : ℝ)) (985759112813/1000000000000 : ℝ) (492879556407/500000000000 : ℝ) (168163526081/1000000000000 : ℝ) (21020440761/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (235/2048 : ℝ)) (985759112813/1000000000000 : ℝ) (492879556407/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (235/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985759112813/1000000000000 : ℝ) (492879556407/500000000000 : ℝ) (496439778203/500000000000 : ℝ) (992879556407/1000000000000 : ℝ) (992854023919/1000000000000 : ℝ) (12410675299/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (235/2048 : ℝ)) 1 (496439778203/500000000000 : ℝ) (992879556407/1000000000000 : ℝ) (992854023919/1000000000000 : ℝ) (12410675299/12500000000 : ℝ) (496433395081/500000000000 : ℝ) (248216697541/250000000000 : ℝ) (3102708719/3125000000 : ℝ) (496433395041/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (235/2048 : ℝ)) 2 (496433395081/500000000000 : ℝ) (248216697541/250000000000 : ℝ) (3102708719/3125000000 : ℝ) (496433395041/500000000000 : ℝ) (992866790121/1000000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (235/2048 : ℝ)) 3 (992866790121/1000000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (235/2048 : ℝ)) 4 (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (235/2048 : ℝ)) 5 (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (235/2048 : ℝ)) 6 (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (235/2048 : ℝ)) 7 (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (235/2048 : ℝ))) (168163526081/1000000000000 : ℝ) (21020440761/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (235/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (168163526081/1000000000000 : ℝ) (21020440761/125000000000 : ℝ) (3650511019/6250000000 : ℝ) (146020440761/250000000000 : ℝ) (51259682939/125000000000 : ℝ) (205038731761/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (235/2048 : ℝ))) 1 (3650511019/6250000000 : ℝ) (146020440761/250000000000 : ℝ) (51259682939/125000000000 : ℝ) (205038731761/500000000000 : ℝ) (124269903319/250000000000 : ℝ) (497079613283/1000000000000 : ℝ) (61175818327/125000000000 : ℝ) (3915252373/8000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (235/2048 : ℝ))) 2 (124269903319/250000000000 : ℝ) (497079613283/1000000000000 : ℝ) (61175818327/125000000000 : ℝ) (3915252373/8000000000 : ℝ) (246621539973/500000000000 : ℝ) (246621539977/500000000000 : ℝ) (493228159097/1000000000000 : ℝ) (246614079553/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (235/2048 : ℝ))) 3 (246621539973/500000000000 : ℝ) (246621539977/500000000000 : ℝ) (493228159097/1000000000000 : ℝ) (246614079553/500000000000 : ℝ) (493235619521/1000000000000 : ℝ) (49323561953/100000000000 : ℝ) (98647123893/200000000000 : ℝ) (246617809737/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (235/2048 : ℝ))) 4 (493235619521/1000000000000 : ℝ) (49323561953/100000000000 : ℝ) (98647123893/200000000000 : ℝ) (246617809737/500000000000 : ℝ) (493235619493/1000000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (235/2048 : ℝ))) 5 (493235619493/1000000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (235/2048 : ℝ))) 6 (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (235/2048 : ℝ))) 7 (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (235/2048 : ℝ)) hmem 8 (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (235/2048 : ℝ))) hcmem 8 (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (235/2048 : ℝ)) (24821669753/25000000000 : ℝ) (992866790123/1000000000000 : ℝ) (123308904873/250000000000 : ℝ) (246617809751/500000000000 : ℝ) (195084755339/250000000000 : ℝ) (12192797209/15625000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0034_exp_lower
  have heNumeric : (2055372903141/1000000000000 : ℝ)/4 ≤ Real.exp (-665837068251/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055372903141/1000000000000 : ℝ)/4 ≤ Real.exp ((469/4096 : ℝ)-(12192797209/15625000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (469/4096 : ℝ) (235/2048 : ℝ) (12192797209/15625000000 : ℝ) (2055372903141/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0035; no trusted numerical premise.
theorem cover8_leaf0035_exp_radius : (998204890727337809/1000000000000000000 : ℝ) ≤ Real.exp ((-471/32768 : ℝ)/8) ∧ Real.exp ((-471/32768 : ℝ)/8) ≤ (99820489072733781/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-471/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0035_exp_lower : (184027546740313369/200000000000000000 : ℝ) ≤ Real.exp ((-133171055359/200000000000 : ℝ)/8) ∧ Real.exp ((-133171055359/200000000000 : ℝ)/8) ≤ (460068866850783423/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133171055359/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0035_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027667739067/500000000000 : ℝ) ≤ 4*Real.exp (235/2048 : ℝ)*Real.exp (-mu (radius 8 (471/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027667739067/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (471/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0035_exp_radius
  have hrNumeric : (985729030291/1000000000000 : ℝ) ≤ Real.exp (-471/32768 : ℝ) ∧ Real.exp (-471/32768 : ℝ) ≤ (246432257573/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985729030291/1000000000000 : ℝ) ≤ (radius 8 (471/4096 : ℝ)) ∧ (radius 8 (471/4096 : ℝ)) ≤ (246432257573/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (471/4096 : ℝ)) (985729030291/1000000000000 : ℝ) (246432257573/250000000000 : ℝ) (168339772007/1000000000000 : ℝ) (84169886007/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (471/4096 : ℝ)) (985729030291/1000000000000 : ℝ) (246432257573/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (471/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985729030291/1000000000000 : ℝ) (246432257573/250000000000 : ℝ) (198572903029/200000000000 : ℝ) (496432257573/500000000000 : ℝ) (248209718571/250000000000 : ℝ) (496419437143/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (471/4096 : ℝ)) 1 (198572903029/200000000000 : ℝ) (496432257573/500000000000 : ℝ) (248209718571/250000000000 : ℝ) (496419437143/500000000000 : ℝ) (496425847357/500000000000 : ℝ) (248212923679/250000000000 : ℝ) (992851694631/1000000000000 : ℝ) (496425847317/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (471/4096 : ℝ)) 2 (496425847357/500000000000 : ℝ) (248212923679/250000000000 : ℝ) (992851694631/1000000000000 : ℝ) (496425847317/500000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (471/4096 : ℝ)) 3 (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (471/4096 : ℝ)) 4 (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (471/4096 : ℝ)) 5 (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (471/4096 : ℝ)) 6 (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (471/4096 : ℝ)) 7 (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (471/4096 : ℝ))) (168339772007/1000000000000 : ℝ) (84169886007/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (471/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (168339772007/1000000000000 : ℝ) (84169886007/500000000000 : ℝ) (584169886003/1000000000000 : ℝ) (584169886007/1000000000000 : ℝ) (410292300691/1000000000000 : ℝ) (410292300701/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (471/4096 : ℝ))) 1 (584169886003/1000000000000 : ℝ) (584169886007/1000000000000 : ℝ) (410292300691/1000000000000 : ℝ) (410292300701/1000000000000 : ℝ) (497231093347/1000000000000 : ℝ) (248615546677/500000000000 : ℝ) (489571656167/1000000000000 : ℝ) (30598228511/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (471/4096 : ℝ))) 2 (497231093347/1000000000000 : ℝ) (248615546677/500000000000 : ℝ) (489571656167/1000000000000 : ℝ) (30598228511/62500000000 : ℝ) (493401374757/1000000000000 : ℝ) (98680274953/200000000000 : ℝ) (493386511639/1000000000000 : ℝ) (15418328489/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (471/4096 : ℝ))) 3 (493401374757/1000000000000 : ℝ) (98680274953/200000000000 : ℝ) (493386511639/1000000000000 : ℝ) (15418328489/31250000000 : ℝ) (246696971599/500000000000 : ℝ) (493393943207/1000000000000 : ℝ) (246696971571/500000000000 : ℝ) (493393943151/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (471/4096 : ℝ))) 4 (246696971599/500000000000 : ℝ) (493393943207/1000000000000 : ℝ) (246696971571/500000000000 : ℝ) (493393943151/1000000000000 : ℝ) (49339394317/100000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (471/4096 : ℝ))) 5 (49339394317/100000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (471/4096 : ℝ))) 6 (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (471/4096 : ℝ))) 7 (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (471/4096 : ℝ)) hmem 8 (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (471/4096 : ℝ))) hcmem 8 (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (471/4096 : ℝ)) (62053230917/62500000000 : ℝ) (39714067787/40000000000 : ℝ) (493393943169/1000000000000 : ℝ) (493393943179/1000000000000 : ℝ) (390300685263/500000000000 : ℝ) (156120274109/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0035_exp_lower
  have heNumeric : (1027667739067/500000000000 : ℝ)/4 ≤ Real.exp (-133171055359/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027667739067/500000000000 : ℝ)/4 ≤ Real.exp ((235/2048 : ℝ)-(156120274109/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (235/2048 : ℝ) (471/4096 : ℝ) (156120274109/200000000000 : ℝ) (1027667739067/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0036; no trusted numerical premise.
theorem cover8_leaf0036_exp_radius : (499100541442566753/500000000000000000 : ℝ) ≤ Real.exp ((-59/4096 : ℝ)/8) ∧ Real.exp ((-59/4096 : ℝ)/8) ≤ (998201082885133507/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-59/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0036_exp_lower : (230033920793854217/250000000000000000 : ℝ) ≤ Real.exp ((-83234138101/125000000000 : ℝ)/8) ∧ Real.exp ((-83234138101/125000000000 : ℝ)/8) ≤ (920135683175416869/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83234138101/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0036_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055298835913/1000000000000 : ℝ) ≤ 4*Real.exp (471/4096 : ℝ)*Real.exp (-mu (radius 8 (59/512 : ℝ))) ∧ (20549/10000 : ℝ) < (2055298835913/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (59/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0036_exp_radius
  have hrNumeric : (61606184293/62500000000 : ℝ) ≤ Real.exp (-59/4096 : ℝ) ∧ Real.exp (-59/4096 : ℝ) ≤ (985698948689/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61606184293/62500000000 : ℝ) ≤ (radius 8 (59/512 : ℝ)) ∧ (radius 8 (59/512 : ℝ)) ≤ (985698948689/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (59/512 : ℝ)) (61606184293/62500000000 : ℝ) (985698948689/1000000000000 : ℝ) (168515822857/1000000000000 : ℝ) (10532238929/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (59/512 : ℝ)) (61606184293/62500000000 : ℝ) (985698948689/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (59/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61606184293/62500000000 : ℝ) (985698948689/1000000000000 : ℝ) (124106184293/125000000000 : ℝ) (198569894869/200000000000 : ℝ) (992823724881/1000000000000 : ℝ) (992823724883/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (59/512 : ℝ)) 1 (124106184293/125000000000 : ℝ) (198569894869/200000000000 : ℝ) (992823724881/1000000000000 : ℝ) (992823724883/1000000000000 : ℝ) (248209149903/250000000000 : ℝ) (496418299807/500000000000 : ℝ) (992836599529/1000000000000 : ℝ) (992836599531/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (59/512 : ℝ)) 2 (248209149903/250000000000 : ℝ) (496418299807/500000000000 : ℝ) (992836599529/1000000000000 : ℝ) (992836599531/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (59/512 : ℝ)) 3 (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (59/512 : ℝ)) 4 (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (59/512 : ℝ)) 5 (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (59/512 : ℝ)) 6 (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (59/512 : ℝ)) 7 (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (59/512 : ℝ))) (168515822857/1000000000000 : ℝ) (10532238929/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (59/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (168515822857/1000000000000 : ℝ) (10532238929/62500000000 : ℝ) (146064477857/250000000000 : ℝ) (73032238929/125000000000 : ℝ) (410506787833/1000000000000 : ℝ) (205253393921/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (59/512 : ℝ))) 1 (146064477857/250000000000 : ℝ) (73032238929/125000000000 : ℝ) (410506787833/1000000000000 : ℝ) (205253393921/500000000000 : ℝ) (49738234963/100000000000 : ℝ) (497382349637/1000000000000 : ℝ) (244868249517/500000000000 : ℝ) (244868249521/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (59/512 : ℝ))) 2 (49738234963/100000000000 : ℝ) (497382349637/1000000000000 : ℝ) (244868249517/500000000000 : ℝ) (244868249521/500000000000 : ℝ) (123389856083/250000000000 : ℝ) (24677971217/50000000000 : ℝ) (6169307733/12500000000 : ℝ) (493544618649/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (59/512 : ℝ))) 3 (123389856083/250000000000 : ℝ) (24677971217/50000000000 : ℝ) (6169307733/12500000000 : ℝ) (493544618649/1000000000000 : ℝ) (246776010743/500000000000 : ℝ) (98710404299/200000000000 : ℝ) (49355202143/100000000000 : ℝ) (493552021439/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (59/512 : ℝ))) 4 (246776010743/500000000000 : ℝ) (98710404299/200000000000 : ℝ) (49355202143/100000000000 : ℝ) (493552021439/1000000000000 : ℝ) (246776010729/500000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (59/512 : ℝ))) 5 (246776010729/500000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (59/512 : ℝ))) 6 (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (59/512 : ℝ))) 7 (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (59/512 : ℝ)) hmem 8 (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (59/512 : ℝ))) hcmem 8 (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (59/512 : ℝ)) (99283659957/100000000000 : ℝ) (992836599573/1000000000000 : ℝ) (493552021457/1000000000000 : ℝ) (493552021467/1000000000000 : ℝ) (195215834791/250000000000 : ℝ) (780863339183/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0036_exp_lower
  have heNumeric : (2055298835913/1000000000000 : ℝ)/4 ≤ Real.exp (-83234138101/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055298835913/1000000000000 : ℝ)/4 ≤ Real.exp ((471/4096 : ℝ)-(780863339183/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (471/4096 : ℝ) (59/512 : ℝ) (780863339183/1000000000000 : ℝ) (2055298835913/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0037; no trusted numerical premise.
theorem cover8_leaf0037_exp_radius : (998197275057454939/1000000000000000000 : ℝ) ≤ Real.exp ((-473/32768 : ℝ)/8) ∧ Real.exp ((-473/32768 : ℝ)/8) ≤ (49909863752872747/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-473/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0037_exp_lower : (230033419064081247/250000000000000000 : ℝ) ≤ Real.exp ((-166472638431/250000000000 : ℝ)/8) ∧ Real.exp ((-166472638431/250000000000 : ℝ)/8) ≤ (920133676256324989/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166472638431/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0037_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055262973489/1000000000000 : ℝ) ≤ 4*Real.exp (59/512 : ℝ)*Real.exp (-mu (radius 8 (473/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2055262973489/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (473/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0037_exp_radius
  have hrNumeric : (492834434001/500000000000 : ℝ) ≤ Real.exp (-473/32768 : ℝ) ∧ Real.exp (-473/32768 : ℝ) ≤ (985668868003/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492834434001/500000000000 : ℝ) ≤ (radius 8 (473/4096 : ℝ)) ∧ (radius 8 (473/4096 : ℝ)) ≤ (985668868003/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (473/4096 : ℝ)) (492834434001/500000000000 : ℝ) (985668868003/1000000000000 : ℝ) (84345839627/500000000000 : ℝ) (168691679261/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (473/4096 : ℝ)) (492834434001/500000000000 : ℝ) (985668868003/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (473/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492834434001/500000000000 : ℝ) (985668868003/1000000000000 : ℝ) (992834434001/1000000000000 : ℝ) (496417217001/500000000000 : ℝ) (992808575709/1000000000000 : ℝ) (99280857571/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (473/4096 : ℝ)) 1 (992834434001/1000000000000 : ℝ) (496417217001/500000000000 : ℝ) (992808575709/1000000000000 : ℝ) (99280857571/100000000000 : ℝ) (198564300971/200000000000 : ℝ) (124102688107/125000000000 : ℝ) (99282150477/100000000000 : ℝ) (248205376193/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (473/4096 : ℝ)) 2 (198564300971/200000000000 : ℝ) (124102688107/125000000000 : ℝ) (99282150477/100000000000 : ℝ) (248205376193/250000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (473/4096 : ℝ)) 3 (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (473/4096 : ℝ)) 4 (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (473/4096 : ℝ)) 5 (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (473/4096 : ℝ)) 6 (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (473/4096 : ℝ)) 7 (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (473/4096 : ℝ))) (84345839627/500000000000 : ℝ) (168691679261/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (473/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (84345839627/500000000000 : ℝ) (168691679261/1000000000000 : ℝ) (584345839627/1000000000000 : ℝ) (584345839631/1000000000000 : ℝ) (410720926243/1000000000000 : ℝ) (102680231563/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (473/4096 : ℝ))) 1 (584345839627/1000000000000 : ℝ) (584345839631/1000000000000 : ℝ) (410720926243/1000000000000 : ℝ) (102680231563/250000000000 : ℝ) (99506676587/200000000000 : ℝ) (248766691471/500000000000 : ℝ) (122475269059/250000000000 : ℝ) (122475269061/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (473/4096 : ℝ))) 2 (99506676587/200000000000 : ℝ) (248766691471/500000000000 : ℝ) (122475269059/250000000000 : ℝ) (122475269061/250000000000 : ℝ) (98743445917/200000000000 : ℝ) (493717229593/1000000000000 : ℝ) (493702481017/1000000000000 : ℝ) (246851240513/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (473/4096 : ℝ))) 3 (98743445917/200000000000 : ℝ) (493717229593/1000000000000 : ℝ) (493702481017/1000000000000 : ℝ) (246851240513/500000000000 : ℝ) (493709855301/1000000000000 : ℝ) (49370985531/100000000000 : ℝ) (98741971049/200000000000 : ℝ) (98741971051/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (473/4096 : ℝ))) 4 (493709855301/1000000000000 : ℝ) (49370985531/100000000000 : ℝ) (98741971049/200000000000 : ℝ) (98741971051/200000000000 : ℝ) (493709855273/1000000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (473/4096 : ℝ))) 5 (493709855273/1000000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (473/4096 : ℝ))) 6 (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (473/4096 : ℝ))) 7 (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (473/4096 : ℝ)) hmem 8 (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (473/4096 : ℝ))) hcmem 8 (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (473/4096 : ℝ)) (248205376203/250000000000 : ℝ) (496410752407/500000000000 : ℝ) (61713731909/125000000000 : ℝ) (493709855283/1000000000000 : ℝ) (12205077011/15625000000 : ℝ) (195281232181/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0037_exp_lower
  have heNumeric : (2055262973489/1000000000000 : ℝ)/4 ≤ Real.exp (-166472638431/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055262973489/1000000000000 : ℝ)/4 ≤ Real.exp ((59/512 : ℝ)-(195281232181/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (59/512 : ℝ) (473/4096 : ℝ) (195281232181/250000000000 : ℝ) (2055262973489/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0038; no trusted numerical premise.
theorem cover8_leaf0038_exp_radius : (199638693448860411/200000000000000000 : ℝ) ≤ Real.exp ((-237/16384 : ℝ)/8) ∧ Real.exp ((-237/16384 : ℝ)/8) ≤ (124774183405537757/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-237/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0038_exp_lower : (92013171278390297/100000000000000000 : ℝ) ≤ Real.exp ((-133181524987/200000000000 : ℝ)/8) ∧ Real.exp ((-133181524987/200000000000 : ℝ)/8) ≤ (920131712783902971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133181524987/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0038_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055227887961/1000000000000 : ℝ) ≤ 4*Real.exp (473/4096 : ℝ)*Real.exp (-mu (radius 8 (237/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055227887961/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (237/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0038_exp_radius
  have hrNumeric : (492819394117/500000000000 : ℝ) ≤ Real.exp (-237/16384 : ℝ) ∧ Real.exp (-237/16384 : ℝ) ≤ (197127757647/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492819394117/500000000000 : ℝ) ≤ (radius 8 (237/2048 : ℝ)) ∧ (radius 8 (237/2048 : ℝ)) ≤ (197127757647/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (237/2048 : ℝ)) (492819394117/500000000000 : ℝ) (197127757647/200000000000 : ℝ) (844336709/5000000000 : ℝ) (84433670903/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (237/2048 : ℝ)) (492819394117/500000000000 : ℝ) (197127757647/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (237/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492819394117/500000000000 : ℝ) (197127757647/200000000000 : ℝ) (992819394117/1000000000000 : ℝ) (496409697059/500000000000 : ℝ) (62049589173/62500000000 : ℝ) (992793426769/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (237/2048 : ℝ)) 1 (992819394117/1000000000000 : ℝ) (496409697059/500000000000 : ℝ) (62049589173/62500000000 : ℝ) (992793426769/1000000000000 : ℝ) (496403205221/500000000000 : ℝ) (248201602611/250000000000 : ℝ) (992806410357/1000000000000 : ℝ) (992806410359/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (237/2048 : ℝ)) 2 (496403205221/500000000000 : ℝ) (248201602611/250000000000 : ℝ) (992806410357/1000000000000 : ℝ) (992806410359/1000000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (237/2048 : ℝ)) 3 (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (237/2048 : ℝ)) 4 (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (237/2048 : ℝ)) 5 (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (237/2048 : ℝ)) 6 (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (237/2048 : ℝ)) 7 (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (237/2048 : ℝ))) (844336709/5000000000 : ℝ) (84433670903/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (237/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (844336709/5000000000 : ℝ) (84433670903/500000000000 : ℝ) (5844336709/10000000000 : ℝ) (584433670903/1000000000000 : ℝ) (410934717199/1000000000000 : ℝ) (51366839651/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (237/2048 : ℝ))) 1 (5844336709/10000000000 : ℝ) (584433670903/1000000000000 : ℝ) (410934717199/1000000000000 : ℝ) (51366839651/125000000000 : ℝ) (497684194049/1000000000000 : ℝ) (62210524257/125000000000 : ℝ) (122516347193/250000000000 : ℝ) (24503269439/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (237/2048 : ℝ))) 2 (497684194049/1000000000000 : ℝ) (62210524257/125000000000 : ℝ) (122516347193/250000000000 : ℝ) (24503269439/50000000000 : ℝ) (49387479141/100000000000 : ℝ) (246937395709/500000000000 : ℝ) (246930049833/500000000000 : ℝ) (246930049837/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (237/2048 : ℝ))) 3 (49387479141/100000000000 : ℝ) (246937395709/500000000000 : ℝ) (246930049833/500000000000 : ℝ) (246930049837/500000000000 : ℝ) (246933722769/500000000000 : ℝ) (246933722773/500000000000 : ℝ) (493867445483/1000000000000 : ℝ) (123466861373/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (237/2048 : ℝ))) 4 (246933722769/500000000000 : ℝ) (246933722773/500000000000 : ℝ) (493867445483/1000000000000 : ℝ) (123466861373/250000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (237/2048 : ℝ))) 5 (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (237/2048 : ℝ))) 6 (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (237/2048 : ℝ))) 7 (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (237/2048 : ℝ)) hmem 8 (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (237/2048 : ℝ))) hcmem 8 (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (237/2048 : ℝ)) (992806410399/1000000000000 : ℝ) (496403205201/500000000000 : ℝ) (49386744551/100000000000 : ℝ) (493867445519/1000000000000 : ℝ) (781386140543/1000000000000 : ℝ) (9767326757/12500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0038_exp_lower
  have heNumeric : (2055227887961/1000000000000 : ℝ)/4 ≤ Real.exp (-133181524987/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055227887961/1000000000000 : ℝ)/4 ≤ Real.exp ((473/4096 : ℝ)-(9767326757/12500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (473/4096 : ℝ) (237/2048 : ℝ) (9767326757/12500000000 : ℝ) (2055227887961/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0039; no trusted numerical premise.
theorem cover8_leaf0039_exp_radius : (499094829722837399/500000000000000000 : ℝ) ≤ Real.exp ((-475/32768 : ℝ)/8) ∧ Real.exp ((-475/32768 : ℝ)/8) ≤ (998189659445674799/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-475/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0039_exp_lower : (460064896298540009/500000000000000000 : ℝ) ≤ Real.exp ((-665924319839/1000000000000 : ℝ)/8) ∧ Real.exp ((-665924319839/1000000000000 : ℝ)/8) ≤ (920129792597080019/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665924319839/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0039_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (411038715283/200000000000 : ℝ) ≤ 4*Real.exp (237/2048 : ℝ)*Real.exp (-mu (radius 8 (475/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (411038715283/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (475/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0039_exp_radius
  have hrNumeric : (197121741877/200000000000 : ℝ) ≤ Real.exp (-475/32768 : ℝ) ∧ Real.exp (-475/32768 : ℝ) ≤ (492804354693/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (197121741877/200000000000 : ℝ) ≤ (radius 8 (475/4096 : ℝ)) ∧ (radius 8 (475/4096 : ℝ)) ≤ (492804354693/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (475/4096 : ℝ)) (197121741877/200000000000 : ℝ) (492804354693/500000000000 : ℝ) (169042811093/1000000000000 : ℝ) (1690428111/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (475/4096 : ℝ)) (197121741877/200000000000 : ℝ) (492804354693/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (475/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (197121741877/200000000000 : ℝ) (492804354693/500000000000 : ℝ) (248201088673/250000000000 : ℝ) (992804354693/1000000000000 : ℝ) (496389139029/500000000000 : ℝ) (49638913903/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (475/4096 : ℝ)) 1 (248201088673/250000000000 : ℝ) (992804354693/1000000000000 : ℝ) (496389139029/500000000000 : ℝ) (49638913903/50000000000 : ℝ) (7942330531/8000000000 : ℝ) (992791316377/1000000000000 : ℝ) (992791316289/1000000000000 : ℝ) (992791316291/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (475/4096 : ℝ)) 2 (7942330531/8000000000 : ℝ) (992791316377/1000000000000 : ℝ) (992791316289/1000000000000 : ℝ) (992791316291/1000000000000 : ℝ) (248197829083/250000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (475/4096 : ℝ)) 3 (248197829083/250000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (475/4096 : ℝ)) 4 (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (475/4096 : ℝ)) 5 (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (475/4096 : ℝ)) 6 (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (475/4096 : ℝ)) 7 (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (475/4096 : ℝ))) (169042811093/1000000000000 : ℝ) (1690428111/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (475/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (169042811093/1000000000000 : ℝ) (1690428111/10000000000 : ℝ) (292260702773/500000000000 : ℝ) (11690428111/20000000000 : ℝ) (102787040493/250000000000 : ℝ) (411148161981/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (475/4096 : ℝ))) 1 (292260702773/500000000000 : ℝ) (11690428111/20000000000 : ℝ) (102787040493/250000000000 : ℝ) (411148161981/1000000000000 : ℝ) (497834783759/1000000000000 : ℝ) (248917391883/500000000000 : ℝ) (245114718817/500000000000 : ℝ) (245114718821/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (475/4096 : ℝ))) 2 (497834783759/1000000000000 : ℝ) (248917391883/500000000000 : ℝ) (245114718817/500000000000 : ℝ) (245114718821/500000000000 : ℝ) (61754013837/125000000000 : ℝ) (30877006919/62500000000 : ℝ) (494017475477/1000000000000 : ℝ) (98803495097/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (475/4096 : ℝ))) 3 (61754013837/125000000000 : ℝ) (30877006919/62500000000 : ℝ) (494017475477/1000000000000 : ℝ) (98803495097/200000000000 : ℝ) (247012396543/500000000000 : ℝ) (98804958619/200000000000 : ℝ) (61753099129/125000000000 : ℝ) (494024793041/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (475/4096 : ℝ))) 4 (247012396543/500000000000 : ℝ) (98804958619/200000000000 : ℝ) (61753099129/125000000000 : ℝ) (494024793041/1000000000000 : ℝ) (494024793059/1000000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (475/4096 : ℝ))) 5 (494024793059/1000000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (475/4096 : ℝ))) 6 (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (475/4096 : ℝ))) 7 (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (475/4096 : ℝ)) hmem 8 (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (475/4096 : ℝ))) hcmem 8 (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (475/4096 : ℝ)) (992791316331/1000000000000 : ℝ) (496395658167/500000000000 : ℝ) (247012396529/500000000000 : ℝ) (123506198267/250000000000 : ℝ) (78164697607/100000000000 : ℝ) (781646976089/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0039_exp_lower
  have heNumeric : (411038715283/200000000000 : ℝ)/4 ≤ Real.exp (-665924319839/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (411038715283/200000000000 : ℝ)/4 ≤ Real.exp ((237/2048 : ℝ)-(781646976089/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (237/2048 : ℝ) (475/4096 : ℝ) (781646976089/1000000000000 : ℝ) (411038715283/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0040; no trusted numerical premise.
theorem cover8_leaf0040_exp_radius : (998185851661573111/1000000000000000000 : ℝ) ≤ Real.exp ((-119/8192 : ℝ)/8) ∧ Real.exp ((-119/8192 : ℝ)/8) ≤ (124773231457696639/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-119/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0040_exp_lower : (36805116621368709/40000000000000000 : ℝ) ≤ Real.exp ((-665940639839/1000000000000 : ℝ)/8) ∧ Real.exp ((-665940639839/1000000000000 : ℝ)/8) ≤ (460063957767108863/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665940639839/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0040_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055160035929/1000000000000 : ℝ) ≤ 4*Real.exp (475/4096 : ℝ)*Real.exp (-mu (radius 8 (119/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2055160035929/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (119/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0040_exp_radius
  have hrNumeric : (985578631453/1000000000000 : ℝ) ≤ Real.exp (-119/8192 : ℝ) ∧ Real.exp (-119/8192 : ℝ) ≤ (492789315727/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985578631453/1000000000000 : ℝ) ≤ (radius 8 (119/1024 : ℝ)) ∧ (radius 8 (119/1024 : ℝ)) ≤ (492789315727/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (119/1024 : ℝ)) (985578631453/1000000000000 : ℝ) (492789315727/500000000000 : ℝ) (42304521937/250000000000 : ℝ) (33843617551/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (119/1024 : ℝ)) (985578631453/1000000000000 : ℝ) (492789315727/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (119/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985578631453/1000000000000 : ℝ) (492789315727/500000000000 : ℝ) (496394657863/500000000000 : ℝ) (992789315727/1000000000000 : ℝ) (992763129579/1000000000000 : ℝ) (992763129581/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (119/1024 : ℝ)) 1 (496394657863/500000000000 : ℝ) (992789315727/1000000000000 : ℝ) (992763129579/1000000000000 : ℝ) (992763129581/1000000000000 : ℝ) (248194055663/250000000000 : ℝ) (496388111327/500000000000 : ℝ) (496388111283/500000000000 : ℝ) (124097027821/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (119/1024 : ℝ)) 2 (248194055663/250000000000 : ℝ) (496388111327/500000000000 : ℝ) (496388111283/500000000000 : ℝ) (124097027821/125000000000 : ℝ) (992776222609/1000000000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (119/1024 : ℝ)) 3 (992776222609/1000000000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (119/1024 : ℝ)) 4 (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (119/1024 : ℝ)) 5 (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (119/1024 : ℝ)) 6 (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (119/1024 : ℝ)) 7 (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (119/1024 : ℝ))) (42304521937/250000000000 : ℝ) (33843617551/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (119/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (42304521937/250000000000 : ℝ) (33843617551/200000000000 : ℝ) (292304521937/500000000000 : ℝ) (292304521939/500000000000 : ℝ) (205680630923/500000000000 : ℝ) (12855039433/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (119/1024 : ℝ))) 1 (292304521937/500000000000 : ℝ) (292304521939/500000000000 : ℝ) (205680630923/500000000000 : ℝ) (12855039433/31250000000 : ℝ) (24899257643/50000000000 : ℝ) (497985152867/1000000000000 : ℝ) (245196611913/500000000000 : ℝ) (245196611917/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (119/1024 : ℝ))) 2 (24899257643/50000000000 : ℝ) (497985152867/1000000000000 : ℝ) (245196611913/500000000000 : ℝ) (245196611917/500000000000 : ℝ) (494189188343/1000000000000 : ℝ) (494189188351/1000000000000 : ℝ) (61771826169/125000000000 : ℝ) (6177182617/12500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (119/1024 : ℝ))) 3 (494189188343/1000000000000 : ℝ) (494189188351/1000000000000 : ℝ) (61771826169/125000000000 : ℝ) (6177182617/12500000000 : ℝ) (494181898847/1000000000000 : ℝ) (61772737357/125000000000 : ℝ) (494181898793/1000000000000 : ℝ) (247090949401/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (119/1024 : ℝ))) 4 (494181898847/1000000000000 : ℝ) (61772737357/125000000000 : ℝ) (494181898793/1000000000000 : ℝ) (247090949401/500000000000 : ℝ) (24709094941/50000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (119/1024 : ℝ))) 5 (24709094941/50000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (119/1024 : ℝ))) 6 (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (119/1024 : ℝ))) 7 (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (119/1024 : ℝ)) hmem 8 (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (119/1024 : ℝ))) hcmem 8 (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (119/1024 : ℝ)) (62048513913/62500000000 : ℝ) (992776222611/1000000000000 : ℝ) (494181898819/1000000000000 : ℝ) (494181898829/1000000000000 : ℝ) (390953718347/500000000000 : ℝ) (390953718357/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0040_exp_lower
  have heNumeric : (2055160035929/1000000000000 : ℝ)/4 ≤ Real.exp (-665940639839/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055160035929/1000000000000 : ℝ)/4 ≤ Real.exp ((475/4096 : ℝ)-(390953718357/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (475/4096 : ℝ) (119/1024 : ℝ) (390953718357/500000000000 : ℝ) (2055160035929/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0041; no trusted numerical premise.
theorem cover8_leaf0041_exp_radius : (998182043891996941/1000000000000000000 : ℝ) ≤ Real.exp ((-477/32768 : ℝ)/8) ∧ Real.exp ((-477/32768 : ℝ)/8) ≤ (499091021945998471/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-477/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0041_exp_lower : (184025216287450113/200000000000000000 : ℝ) ≤ Real.exp ((-665956586307/1000000000000 : ℝ)/8) ∧ Real.exp ((-665956586307/1000000000000 : ℝ)/8) ≤ (460063040718625283/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665956586307/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0041_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055127263647/1000000000000 : ℝ) ≤ 4*Real.exp (119/1024 : ℝ)*Real.exp (-mu (radius 8 (477/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2055127263647/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (477/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0041_exp_radius
  have hrNumeric : (985548554439/1000000000000 : ℝ) ≤ Real.exp (-477/32768 : ℝ) ∧ Real.exp (-477/32768 : ℝ) ≤ (24638713861/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985548554439/1000000000000 : ℝ) ≤ (radius 8 (477/4096 : ℝ)) ∧ (radius 8 (477/4096 : ℝ)) ≤ (24638713861/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (477/4096 : ℝ)) (985548554439/1000000000000 : ℝ) (24638713861/25000000000 : ℝ) (169393172357/1000000000000 : ℝ) (169393172363/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (477/4096 : ℝ)) (985548554439/1000000000000 : ℝ) (24638713861/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (477/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985548554439/1000000000000 : ℝ) (24638713861/25000000000 : ℝ) (992774277219/1000000000000 : ℝ) (49638713861/50000000000 : ℝ) (248186995333/250000000000 : ℝ) (992747981333/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (477/4096 : ℝ)) 1 (992774277219/1000000000000 : ℝ) (49638713861/50000000000 : ℝ) (248186995333/250000000000 : ℝ) (992747981333/1000000000000 : ℝ) (39710445171/40000000000 : ℝ) (992761129277/1000000000000 : ℝ) (248190282297/250000000000 : ℝ) (99276112919/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (477/4096 : ℝ)) 2 (39710445171/40000000000 : ℝ) (992761129277/1000000000000 : ℝ) (248190282297/250000000000 : ℝ) (99276112919/100000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (477/4096 : ℝ)) 3 (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (477/4096 : ℝ)) 4 (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (477/4096 : ℝ)) 5 (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (477/4096 : ℝ)) 6 (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (477/4096 : ℝ)) 7 (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (477/4096 : ℝ))) (169393172357/1000000000000 : ℝ) (169393172363/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (477/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (169393172357/1000000000000 : ℝ) (169393172363/1000000000000 : ℝ) (292348293089/500000000000 : ℝ) (292348293091/500000000000 : ℝ) (205787009039/500000000000 : ℝ) (205787009043/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (477/4096 : ℝ))) 1 (292348293089/500000000000 : ℝ) (292348293091/500000000000 : ℝ) (205787009039/500000000000 : ℝ) (205787009043/500000000000 : ℝ) (31133456383/62500000000 : ℝ) (249067651067/500000000000 : ℝ) (490556748327/1000000000000 : ℝ) (98111349667/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (477/4096 : ℝ))) 2 (31133456383/62500000000 : ℝ) (249067651067/500000000000 : ℝ) (490556748327/1000000000000 : ℝ) (98111349667/200000000000 : ℝ) (494346025227/1000000000000 : ℝ) (98869205047/200000000000 : ℝ) (494331502171/1000000000000 : ℝ) (494331502179/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (477/4096 : ℝ))) 3 (494346025227/1000000000000 : ℝ) (98869205047/200000000000 : ℝ) (494331502171/1000000000000 : ℝ) (494331502179/1000000000000 : ℝ) (494338763699/1000000000000 : ℝ) (494338763707/1000000000000 : ℝ) (98867752729/200000000000 : ℝ) (247169381827/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (477/4096 : ℝ))) 4 (494338763699/1000000000000 : ℝ) (494338763707/1000000000000 : ℝ) (98867752729/200000000000 : ℝ) (247169381827/500000000000 : ℝ) (61792345459/125000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (477/4096 : ℝ))) 5 (61792345459/125000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (477/4096 : ℝ))) 6 (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (477/4096 : ℝ))) 7 (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (477/4096 : ℝ)) hmem 8 (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (477/4096 : ℝ))) hcmem 8 (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (477/4096 : ℝ)) (992761129231/1000000000000 : ℝ) (496380564617/500000000000 : ℝ) (494338763671/1000000000000 : ℝ) (494338763681/1000000000000 : ℝ) (195541880947/250000000000 : ℝ) (782167523807/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0041_exp_lower
  have heNumeric : (2055127263647/1000000000000 : ℝ)/4 ≤ Real.exp (-665956586307/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055127263647/1000000000000 : ℝ)/4 ≤ Real.exp ((119/1024 : ℝ)-(782167523807/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (119/1024 : ℝ) (477/4096 : ℝ) (782167523807/1000000000000 : ℝ) (2055127263647/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0042; no trusted numerical premise.
theorem cover8_leaf0042_exp_radius : (998178236136946231/1000000000000000000 : ℝ) ≤ Real.exp ((-239/16384 : ℝ)/8) ∧ Real.exp ((-239/16384 : ℝ)/8) ≤ (124772279517118279/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-239/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0042_exp_lower : (92012429014743021/100000000000000000 : ℝ) ≤ Real.exp ((-665972160621/1000000000000 : ℝ)/8) ∧ Real.exp ((-665972160621/1000000000000 : ℝ)/8) ≤ (920124290147430211/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665972160621/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0042_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055095256699/1000000000000 : ℝ) ≤ 4*Real.exp (477/4096 : ℝ)*Real.exp (-mu (radius 8 (239/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055095256699/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (239/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0042_exp_radius
  have hrNumeric : (985518478343/1000000000000 : ℝ) ≤ Real.exp (-239/16384 : ℝ) ∧ Real.exp (-239/16384 : ℝ) ≤ (123189809793/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985518478343/1000000000000 : ℝ) ≤ (radius 8 (239/2048 : ℝ)) ∧ (radius 8 (239/2048 : ℝ)) ≤ (123189809793/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (239/2048 : ℝ)) (985518478343/1000000000000 : ℝ) (123189809793/125000000000 : ℝ) (33913613103/200000000000 : ℝ) (169568065521/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (239/2048 : ℝ)) (985518478343/1000000000000 : ℝ) (123189809793/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (239/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985518478343/1000000000000 : ℝ) (123189809793/125000000000 : ℝ) (992759239171/1000000000000 : ℝ) (248189809793/250000000000 : ℝ) (198546566663/200000000000 : ℝ) (992732833317/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (239/2048 : ℝ)) 1 (992759239171/1000000000000 : ℝ) (248189809793/250000000000 : ℝ) (198546566663/200000000000 : ℝ) (992732833317/1000000000000 : ℝ) (992746036243/1000000000000 : ℝ) (198549207249/200000000000 : ℝ) (198549207231/200000000000 : ℝ) (992746036157/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (239/2048 : ℝ)) 2 (992746036243/1000000000000 : ℝ) (198549207249/200000000000 : ℝ) (198549207231/200000000000 : ℝ) (992746036157/1000000000000 : ℝ) (992746036199/1000000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (239/2048 : ℝ)) 3 (992746036199/1000000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (239/2048 : ℝ)) 4 (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (239/2048 : ℝ)) 5 (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (239/2048 : ℝ)) 6 (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (239/2048 : ℝ)) 7 (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (239/2048 : ℝ))) (33913613103/200000000000 : ℝ) (169568065521/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (239/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (33913613103/200000000000 : ℝ) (169568065521/1000000000000 : ℝ) (584784032757/1000000000000 : ℝ) (584784032761/1000000000000 : ℝ) (411786431921/1000000000000 : ℝ) (41178643193/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (239/2048 : ℝ))) 1 (584784032757/1000000000000 : ℝ) (584784032761/1000000000000 : ℝ) (411786431921/1000000000000 : ℝ) (41178643193/100000000000 : ℝ) (498285232339/1000000000000 : ℝ) (249142616173/500000000000 : ℝ) (245360006059/500000000000 : ℝ) (245360006063/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (239/2048 : ℝ))) 2 (498285232339/1000000000000 : ℝ) (249142616173/500000000000 : ℝ) (245360006059/500000000000 : ℝ) (245360006063/500000000000 : ℝ) (123625655557/250000000000 : ℝ) (123625655559/250000000000 : ℝ) (247244077407/500000000000 : ℝ) (247244077411/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (239/2048 : ℝ))) 3 (123625655557/250000000000 : ℝ) (123625655559/250000000000 : ℝ) (247244077407/500000000000 : ℝ) (247244077411/500000000000 : ℝ) (494495388521/1000000000000 : ℝ) (494495388529/1000000000000 : ℝ) (123623847117/250000000000 : ℝ) (494495388477/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (239/2048 : ℝ))) 4 (494495388521/1000000000000 : ℝ) (494495388529/1000000000000 : ℝ) (123623847117/250000000000 : ℝ) (494495388477/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (239/2048 : ℝ))) 5 (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (239/2048 : ℝ))) 6 (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (239/2048 : ℝ))) 7 (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (239/2048 : ℝ)) hmem 8 (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (239/2048 : ℝ))) hcmem 8 (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (239/2048 : ℝ)) (496373018099/500000000000 : ℝ) (992746036201/1000000000000 : ℝ) (247247694247/500000000000 : ℝ) (494495388503/1000000000000 : ℝ) (97803404841/125000000000 : ℝ) (391213619373/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0042_exp_lower
  have heNumeric : (2055095256699/1000000000000 : ℝ)/4 ≤ Real.exp (-665972160621/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055095256699/1000000000000 : ℝ)/4 ≤ Real.exp ((477/4096 : ℝ)-(391213619373/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (477/4096 : ℝ) (239/2048 : ℝ) (391213619373/500000000000 : ℝ) (2055095256699/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0043; no trusted numerical premise.
theorem cover8_leaf0043_exp_radius : (998174428396420927/1000000000000000000 : ℝ) ≤ Real.exp ((-479/32768 : ℝ)/8) ∧ Real.exp ((-479/32768 : ℝ)/8) ≤ (15596475443694077/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-479/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0043_exp_lower : (230030635376647659/250000000000000000 : ℝ) ≤ Real.exp ((-332993682077/500000000000 : ℝ)/8) ∧ Real.exp ((-332993682077/500000000000 : ℝ)/8) ≤ (920122541506590637/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-332993682077/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0043_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513766003057/250000000000 : ℝ) ≤ 4*Real.exp (239/2048 : ℝ)*Real.exp (-mu (radius 8 (479/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (513766003057/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (479/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0043_exp_radius
  have hrNumeric : (246372100791/250000000000 : ℝ) ≤ Real.exp (-479/32768 : ℝ) ∧ Real.exp (-479/32768 : ℝ) ≤ (197097680633/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246372100791/250000000000 : ℝ) ≤ (radius 8 (479/4096 : ℝ)) ∧ (radius 8 (479/4096 : ℝ)) ≤ (197097680633/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (479/4096 : ℝ)) (246372100791/250000000000 : ℝ) (197097680633/200000000000 : ℝ) (8487138391/50000000000 : ℝ) (169742767827/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (479/4096 : ℝ)) (246372100791/250000000000 : ℝ) (197097680633/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (479/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246372100791/250000000000 : ℝ) (197097680633/200000000000 : ℝ) (496372100791/500000000000 : ℝ) (992744201583/1000000000000 : ℝ) (992717685529/1000000000000 : ℝ) (992717685531/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (479/4096 : ℝ)) 1 (496372100791/500000000000 : ℝ) (992744201583/1000000000000 : ℝ) (992717685529/1000000000000 : ℝ) (992717685531/1000000000000 : ℝ) (198546188711/200000000000 : ℝ) (992730943557/1000000000000 : ℝ) (496365471733/500000000000 : ℝ) (992730943469/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (479/4096 : ℝ)) 2 (198546188711/200000000000 : ℝ) (992730943557/1000000000000 : ℝ) (496365471733/500000000000 : ℝ) (992730943469/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (479/4096 : ℝ)) 3 (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (479/4096 : ℝ)) 4 (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (479/4096 : ℝ)) 5 (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (479/4096 : ℝ)) 6 (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (479/4096 : ℝ)) 7 (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (479/4096 : ℝ))) (8487138391/50000000000 : ℝ) (169742767827/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (479/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8487138391/50000000000 : ℝ) (169742767827/1000000000000 : ℝ) (58487138391/100000000000 : ℝ) (292435691957/500000000000 : ℝ) (411998504633/1000000000000 : ℝ) (205999252321/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (479/4096 : ℝ))) 1 (58487138391/100000000000 : ℝ) (292435691957/500000000000 : ℝ) (411998504633/1000000000000 : ℝ) (205999252321/500000000000 : ℝ) (498434944271/1000000000000 : ℝ) (249217472139/500000000000 : ℝ) (490883016179/1000000000000 : ℝ) (490883016187/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (479/4096 : ℝ))) 2 (498434944271/1000000000000 : ℝ) (249217472139/500000000000 : ℝ) (490883016179/1000000000000 : ℝ) (490883016187/1000000000000 : ℝ) (19786359209/40000000000 : ℝ) (494658980233/1000000000000 : ℝ) (247322284081/500000000000 : ℝ) (494644568171/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (479/4096 : ℝ))) 3 (19786359209/40000000000 : ℝ) (494658980233/1000000000000 : ℝ) (247322284081/500000000000 : ℝ) (494644568171/1000000000000 : ℝ) (494651774193/1000000000000 : ℝ) (247325887101/500000000000 : ℝ) (494651774141/1000000000000 : ℝ) (9893035483/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (479/4096 : ℝ))) 4 (494651774193/1000000000000 : ℝ) (247325887101/500000000000 : ℝ) (494651774141/1000000000000 : ℝ) (9893035483/20000000000 : ℝ) (494651774167/1000000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (479/4096 : ℝ))) 5 (494651774167/1000000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (479/4096 : ℝ))) 6 (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (479/4096 : ℝ))) 7 (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (479/4096 : ℝ)) hmem 8 (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (479/4096 : ℝ))) hcmem 8 (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (479/4096 : ℝ)) (99273094351/100000000000 : ℝ) (992730943513/1000000000000 : ℝ) (247325887083/500000000000 : ℝ) (15457867943/31250000000 : ℝ) (156537316577/200000000000 : ℝ) (97835822863/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0043_exp_lower
  have heNumeric : (513766003057/250000000000 : ℝ)/4 ≤ Real.exp (-332993682077/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513766003057/250000000000 : ℝ)/4 ≤ Real.exp ((239/2048 : ℝ)-(97835822863/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (239/2048 : ℝ) (479/4096 : ℝ) (97835822863/125000000000 : ℝ) (513766003057/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0044; no trusted numerical premise.
theorem cover8_leaf0044_exp_radius : (249542655167605243/250000000000000000 : ℝ) ≤ Real.exp ((-15/1024 : ℝ)/8) ∧ Real.exp ((-15/1024 : ℝ)/8) ≤ (998170620670420973/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-15/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0044_exp_lower : (230030208840063361/250000000000000000 : ℝ) ≤ Real.exp ((-666002198247/1000000000000 : ℝ)/8) ∧ Real.exp ((-666002198247/1000000000000 : ℝ)/8) ≤ (184024167072050689/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666002198247/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0044_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055033527443/1000000000000 : ℝ) ≤ 4*Real.exp (479/4096 : ℝ)*Real.exp (-mu (radius 8 (15/128 : ℝ))) ∧ (20549/10000 : ℝ) < (2055033527443/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (15/128 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0044_exp_radius
  have hrNumeric : (123182291113/125000000000 : ℝ) ≤ Real.exp (-15/1024 : ℝ) ∧ Real.exp (-15/1024 : ℝ) ≤ (197091665781/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123182291113/125000000000 : ℝ) ≤ (radius 8 (15/128 : ℝ)) ∧ (radius 8 (15/128 : ℝ)) ≤ (197091665781/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (15/128 : ℝ)) (123182291113/125000000000 : ℝ) (197091665781/200000000000 : ℝ) (3398345597/20000000000 : ℝ) (169917279857/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (15/128 : ℝ)) (123182291113/125000000000 : ℝ) (197091665781/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (15/128 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123182291113/125000000000 : ℝ) (197091665781/200000000000 : ℝ) (248182291113/250000000000 : ℝ) (992729164453/1000000000000 : ℝ) (124087817247/125000000000 : ℝ) (992702537977/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (15/128 : ℝ)) 1 (248182291113/250000000000 : ℝ) (992729164453/1000000000000 : ℝ) (124087817247/125000000000 : ℝ) (992702537977/1000000000000 : ℝ) (496357925607/500000000000 : ℝ) (198543170243/200000000000 : ℝ) (248178962781/250000000000 : ℝ) (496357925563/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (15/128 : ℝ)) 2 (496357925607/500000000000 : ℝ) (198543170243/200000000000 : ℝ) (248178962781/250000000000 : ℝ) (496357925563/500000000000 : ℝ) (992715851169/1000000000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (15/128 : ℝ)) 3 (992715851169/1000000000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (15/128 : ℝ)) 4 (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (15/128 : ℝ)) 5 (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (15/128 : ℝ)) 6 (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (15/128 : ℝ)) 7 (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (15/128 : ℝ))) (3398345597/20000000000 : ℝ) (169917279857/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (15/128 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3398345597/20000000000 : ℝ) (169917279857/1000000000000 : ℝ) (23398345597/40000000000 : ℝ) (584958639929/1000000000000 : ℝ) (412210237439/1000000000000 : ℝ) (412210237449/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (15/128 : ℝ))) 1 (23398345597/40000000000 : ℝ) (584958639929/1000000000000 : ℝ) (412210237439/1000000000000 : ℝ) (412210237449/1000000000000 : ℝ) (249292219341/500000000000 : ℝ) (498584438689/1000000000000 : ℝ) (491045761467/1000000000000 : ℝ) (122761440369/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (15/128 : ℝ))) 2 (249292219341/500000000000 : ℝ) (498584438689/1000000000000 : ℝ) (491045761467/1000000000000 : ℝ) (122761440369/250000000000 : ℝ) (247407550037/500000000000 : ℝ) (494815100083/1000000000000 : ℝ) (19792029723/40000000000 : ℝ) (123700185771/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (15/128 : ℝ))) 3 (247407550037/500000000000 : ℝ) (494815100083/1000000000000 : ℝ) (19792029723/40000000000 : ℝ) (123700185771/250000000000 : ℝ) (247403960787/500000000000 : ℝ) (30925495099/62500000000 : ℝ) (247403960761/500000000000 : ℝ) (123701980383/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (15/128 : ℝ))) 4 (247403960787/500000000000 : ℝ) (30925495099/62500000000 : ℝ) (247403960761/500000000000 : ℝ) (123701980383/250000000000 : ℝ) (123701980387/250000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (15/128 : ℝ))) 5 (123701980387/250000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (15/128 : ℝ))) 6 (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (15/128 : ℝ))) 7 (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (15/128 : ℝ)) hmem 8 (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (15/128 : ℝ))) hcmem 8 (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (15/128 : ℝ)) (31022370349/31250000000 : ℝ) (992715851171/1000000000000 : ℝ) (494807921547/1000000000000 : ℝ) (247403960779/500000000000 : ℝ) (782945557601/1000000000000 : ℝ) (391472778811/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0044_exp_lower
  have heNumeric : (2055033527443/1000000000000 : ℝ)/4 ≤ Real.exp (-666002198247/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055033527443/1000000000000 : ℝ)/4 ≤ Real.exp ((479/4096 : ℝ)-(391472778811/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (479/4096 : ℝ) (15/128 : ℝ) (391472778811/500000000000 : ℝ) (2055033527443/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0045; no trusted numerical premise.
theorem cover8_leaf0045_exp_radius : (998166812958946311/1000000000000000000 : ℝ) ≤ Real.exp ((-481/32768 : ℝ)/8) ∧ Real.exp ((-481/32768 : ℝ)/8) ≤ (124770851619868289/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-481/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0045_exp_lower : (920119171551071911/1000000000000000000 : ℝ) ≤ Real.exp ((-333008332133/500000000000 : ℝ)/8) ∧ Real.exp ((-333008332133/500000000000 : ℝ)/8) ≤ (115014896443883989/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333008332133/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0045_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128437737469/62500000000 : ℝ) ≤ 4*Real.exp (15/128 : ℝ)*Real.exp (-mu (radius 8 (481/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (128437737469/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (481/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0045_exp_radius
  have hrNumeric : (985428255561/1000000000000 : ℝ) ≤ Real.exp (-481/32768 : ℝ) ∧ Real.exp (-481/32768 : ℝ) ≤ (492714127781/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985428255561/1000000000000 : ℝ) ≤ (radius 8 (481/4096 : ℝ)) ∧ (radius 8 (481/4096 : ℝ)) ≤ (492714127781/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (481/4096 : ℝ)) (985428255561/1000000000000 : ℝ) (492714127781/500000000000 : ℝ) (170091602203/1000000000000 : ℝ) (170091602209/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (481/4096 : ℝ)) (985428255561/1000000000000 : ℝ) (492714127781/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (481/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985428255561/1000000000000 : ℝ) (492714127781/500000000000 : ℝ) (49635706389/50000000000 : ℝ) (992714127781/1000000000000 : ℝ) (248171847663/250000000000 : ℝ) (496343695327/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (481/4096 : ℝ)) 1 (49635706389/50000000000 : ℝ) (992714127781/1000000000000 : ℝ) (248171847663/250000000000 : ℝ) (496343695327/500000000000 : ℝ) (62043797451/62500000000 : ℝ) (496350379609/500000000000 : ℝ) (7941606073/8000000000 : ℝ) (124087594891/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (481/4096 : ℝ)) 2 (62043797451/62500000000 : ℝ) (496350379609/500000000000 : ℝ) (7941606073/8000000000 : ℝ) (124087594891/125000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (481/4096 : ℝ)) 3 (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (481/4096 : ℝ)) 4 (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (481/4096 : ℝ)) 5 (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (481/4096 : ℝ)) 6 (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (481/4096 : ℝ)) 7 (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (481/4096 : ℝ))) (170091602203/1000000000000 : ℝ) (170091602209/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (481/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (170091602203/1000000000000 : ℝ) (170091602209/1000000000000 : ℝ) (585045801101/1000000000000 : ℝ) (117009160221/200000000000 : ℝ) (412421631589/1000000000000 : ℝ) (412421631597/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (481/4096 : ℝ))) 1 (585045801101/1000000000000 : ℝ) (117009160221/200000000000 : ℝ) (412421631589/1000000000000 : ℝ) (412421631597/1000000000000 : ℝ) (99746743269/200000000000 : ℝ) (498733716351/1000000000000 : ℝ) (491208248957/1000000000000 : ℝ) (98241649793/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (481/4096 : ℝ))) 2 (99746743269/200000000000 : ℝ) (498733716351/1000000000000 : ℝ) (491208248957/1000000000000 : ℝ) (98241649793/200000000000 : ℝ) (494970982651/1000000000000 : ℝ) (247485491329/500000000000 : ℝ) (494956680429/1000000000000 : ℝ) (494956680437/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (481/4096 : ℝ))) 3 (494970982651/1000000000000 : ℝ) (247485491329/500000000000 : ℝ) (494956680429/1000000000000 : ℝ) (494956680437/1000000000000 : ℝ) (24748191577/50000000000 : ℝ) (123740957887/250000000000 : ℝ) (7733809867/15625000000 : ℝ) (61870478937/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (481/4096 : ℝ))) 4 (24748191577/50000000000 : ℝ) (123740957887/250000000000 : ℝ) (7733809867/15625000000 : ℝ) (61870478937/125000000000 : ℝ) (247481915757/500000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (481/4096 : ℝ))) 5 (247481915757/500000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (481/4096 : ℝ))) 6 (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (481/4096 : ℝ))) 7 (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (481/4096 : ℝ)) hmem 8 (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (481/4096 : ℝ))) hcmem 8 (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (481/4096 : ℝ)) (99270075917/100000000000 : ℝ) (992700759173/1000000000000 : ℝ) (494963831513/1000000000000 : ℝ) (247481915761/500000000000 : ℝ) (97900520531/125000000000 : ℝ) (391602082133/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0045_exp_lower
  have heNumeric : (128437737469/62500000000 : ℝ)/4 ≤ Real.exp (-333008332133/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128437737469/62500000000 : ℝ)/4 ≤ Real.exp ((15/128 : ℝ)-(391602082133/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (15/128 : ℝ) (481/4096 : ℝ) (391602082133/500000000000 : ℝ) (128437737469/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0046; no trusted numerical premise.
theorem cover8_leaf0046_exp_radius : (998163005261996889/1000000000000000000 : ℝ) ≤ Real.exp ((-241/16384 : ℝ)/8) ∧ Real.exp ((-241/16384 : ℝ)/8) ≤ (99816300526199689/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-241/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0046_exp_lower : (920117549924926719/1000000000000000000 : ℝ) ≤ Real.exp ((-666030763549/1000000000000 : ℝ)/8) ∧ Real.exp ((-666030763549/1000000000000 : ℝ)/8) ≤ (718841835878849/781250000000000 : ℝ) := by
  have h := exp_small_bounds ((-666030763549/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0046_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513743706407/250000000000 : ℝ) ≤ 4*Real.exp (481/4096 : ℝ)*Real.exp (-mu (radius 8 (241/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (513743706407/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (241/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0046_exp_radius
  have hrNumeric : (30793693223/31250000000 : ℝ) ≤ Real.exp (-241/16384 : ℝ) ∧ Real.exp (-241/16384 : ℝ) ≤ (985398183137/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30793693223/31250000000 : ℝ) ≤ (radius 8 (241/2048 : ℝ)) ∧ (radius 8 (241/2048 : ℝ)) ≤ (985398183137/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (241/2048 : ℝ)) (30793693223/31250000000 : ℝ) (985398183137/1000000000000 : ℝ) (34053147091/200000000000 : ℝ) (85132867731/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (241/2048 : ℝ)) (30793693223/31250000000 : ℝ) (985398183137/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (241/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30793693223/31250000000 : ℝ) (985398183137/1000000000000 : ℝ) (62043693223/62500000000 : ℝ) (992699091569/1000000000000 : ℝ) (24816806089/25000000000 : ℝ) (496336121781/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (241/2048 : ℝ)) 1 (62043693223/62500000000 : ℝ) (992699091569/1000000000000 : ℝ) (24816806089/25000000000 : ℝ) (496336121781/500000000000 : ℝ) (248171416891/250000000000 : ℝ) (496342833783/500000000000 : ℝ) (992685667473/1000000000000 : ℝ) (39707426699/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (241/2048 : ℝ)) 2 (248171416891/250000000000 : ℝ) (496342833783/500000000000 : ℝ) (992685667473/1000000000000 : ℝ) (39707426699/40000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (241/2048 : ℝ)) 3 (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (241/2048 : ℝ)) 4 (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (241/2048 : ℝ)) 5 (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (241/2048 : ℝ)) 6 (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (241/2048 : ℝ)) 7 (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (241/2048 : ℝ))) (34053147091/200000000000 : ℝ) (85132867731/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (241/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (34053147091/200000000000 : ℝ) (85132867731/500000000000 : ℝ) (585132867727/1000000000000 : ℝ) (585132867731/1000000000000 : ℝ) (412632688301/1000000000000 : ℝ) (412632688311/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (241/2048 : ℝ))) 1 (585132867727/1000000000000 : ℝ) (585132867731/1000000000000 : ℝ) (412632688301/1000000000000 : ℝ) (412632688311/1000000000000 : ℝ) (249441389007/500000000000 : ℝ) (498882778021/1000000000000 : ℝ) (491370479601/1000000000000 : ℝ) (491370479609/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (241/2048 : ℝ))) 2 (249441389007/500000000000 : ℝ) (498882778021/1000000000000 : ℝ) (491370479601/1000000000000 : ℝ) (491370479609/1000000000000 : ℝ) (495126628807/1000000000000 : ℝ) (99025325763/200000000000 : ℝ) (247556190539/500000000000 : ℝ) (495112381087/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (241/2048 : ℝ))) 3 (495126628807/1000000000000 : ℝ) (99025325763/200000000000 : ℝ) (247556190539/500000000000 : ℝ) (495112381087/1000000000000 : ℝ) (247559752471/500000000000 : ℝ) (495119504951/1000000000000 : ℝ) (495119504891/1000000000000 : ℝ) (4951195049/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (241/2048 : ℝ))) 4 (247559752471/500000000000 : ℝ) (495119504951/1000000000000 : ℝ) (495119504891/1000000000000 : ℝ) (4951195049/10000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (241/2048 : ℝ))) 5 (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (241/2048 : ℝ))) 6 (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (241/2048 : ℝ))) 7 (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (241/2048 : ℝ)) hmem 8 (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (241/2048 : ℝ))) hcmem 8 (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (241/2048 : ℝ)) (496342833759/500000000000 : ℝ) (992685667521/1000000000000 : ℝ) (123779876229/250000000000 : ℝ) (247559752463/500000000000 : ℝ) (156692480831/200000000000 : ℝ) (391731202087/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0046_exp_lower
  have heNumeric : (513743706407/250000000000 : ℝ)/4 ≤ Real.exp (-666030763549/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513743706407/250000000000 : ℝ)/4 ≤ Real.exp ((481/4096 : ℝ)-(391731202087/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (481/4096 : ℝ) (241/2048 : ℝ) (391731202087/500000000000 : ℝ) (513743706407/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0047; no trusted numerical premise.
theorem cover8_leaf0047_exp_radius : (998159197579572651/1000000000000000000 : ℝ) ≤ Real.exp ((-483/32768 : ℝ)/8) ∧ Real.exp ((-483/32768 : ℝ)/8) ≤ (249539799394893163/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-483/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0047_exp_lower : (920115970328165509/1000000000000000000 : ℝ) ≤ Real.exp ((-66604449743/100000000000 : ℝ)/8) ∧ Real.exp ((-66604449743/100000000000 : ℝ)/8) ≤ (92011597032816551/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66604449743/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0047_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027473301521/500000000000 : ℝ) ≤ 4*Real.exp (241/2048 : ℝ)*Real.exp (-mu (radius 8 (483/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027473301521/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (483/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0047_exp_radius
  have hrNumeric : (985368111629/1000000000000 : ℝ) ≤ Real.exp (-483/32768 : ℝ) ∧ Real.exp (-483/32768 : ℝ) ≤ (98536811163/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985368111629/1000000000000 : ℝ) ≤ (radius 8 (483/4096 : ℝ)) ∧ (radius 8 (483/4096 : ℝ)) ≤ (98536811163/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (483/4096 : ℝ)) (985368111629/1000000000000 : ℝ) (98536811163/100000000000 : ℝ) (42609920047/250000000000 : ℝ) (34087936039/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (483/4096 : ℝ)) (985368111629/1000000000000 : ℝ) (98536811163/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (483/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985368111629/1000000000000 : ℝ) (98536811163/100000000000 : ℝ) (496342027907/500000000000 : ℝ) (198536811163/200000000000 : ℝ) (9926570967/10000000000 : ℝ) (992657096701/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (483/4096 : ℝ)) 1 (496342027907/500000000000 : ℝ) (198536811163/200000000000 : ℝ) (9926570967/10000000000 : ℝ) (992657096701/1000000000000 : ℝ) (992670576257/1000000000000 : ℝ) (496335288129/500000000000 : ℝ) (198534115233/200000000000 : ℝ) (992670576167/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (483/4096 : ℝ)) 2 (992670576257/1000000000000 : ℝ) (496335288129/500000000000 : ℝ) (198534115233/200000000000 : ℝ) (992670576167/1000000000000 : ℝ) (992670576211/1000000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (483/4096 : ℝ)) 3 (992670576211/1000000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (483/4096 : ℝ)) 4 (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (483/4096 : ℝ)) 5 (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (483/4096 : ℝ)) 6 (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (483/4096 : ℝ)) 7 (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (483/4096 : ℝ))) (42609920047/250000000000 : ℝ) (34087936039/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (483/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (42609920047/250000000000 : ℝ) (34087936039/200000000000 : ℝ) (292609920047/500000000000 : ℝ) (292609920049/500000000000 : ℝ) (206421704399/500000000000 : ℝ) (412843408807/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (483/4096 : ℝ))) 1 (292609920047/500000000000 : ℝ) (292609920049/500000000000 : ℝ) (206421704399/500000000000 : ℝ) (412843408807/1000000000000 : ℝ) (249515812223/500000000000 : ℝ) (499031624453/1000000000000 : ℝ) (491532454351/1000000000000 : ℝ) (491532454359/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (483/4096 : ℝ))) 2 (249515812223/500000000000 : ℝ) (499031624453/1000000000000 : ℝ) (491532454351/1000000000000 : ℝ) (491532454359/1000000000000 : ℝ) (247641019699/500000000000 : ℝ) (247641019703/500000000000 : ℝ) (12381696147/25000000000 : ℝ) (1934640023/3906250000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (483/4096 : ℝ))) 3 (247641019699/500000000000 : ℝ) (247641019703/500000000000 : ℝ) (12381696147/25000000000 : ℝ) (1934640023/3906250000 : ℝ) (495274942639/1000000000000 : ℝ) (495274942647/1000000000000 : ℝ) (123818735647/250000000000 : ℝ) (495274942597/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (483/4096 : ℝ))) 4 (495274942639/1000000000000 : ℝ) (495274942647/1000000000000 : ℝ) (123818735647/250000000000 : ℝ) (495274942597/1000000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (483/4096 : ℝ))) 5 (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (483/4096 : ℝ))) 6 (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (483/4096 : ℝ))) 7 (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (483/4096 : ℝ)) hmem 8 (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (483/4096 : ℝ))) hcmem 8 (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (483/4096 : ℝ)) (99267057621/100000000000 : ℝ) (992670576213/1000000000000 : ℝ) (495274942613/1000000000000 : ℝ) (247637471311/500000000000 : ℝ) (391860139331/500000000000 : ℝ) (19593006967/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0047_exp_lower
  have heNumeric : (1027473301521/500000000000 : ℝ)/4 ≤ Real.exp (-66604449743/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027473301521/500000000000 : ℝ)/4 ≤ Real.exp ((241/2048 : ℝ)-(19593006967/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (241/2048 : ℝ) (483/4096 : ℝ) (19593006967/25000000000 : ℝ) (1027473301521/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0048; no trusted numerical premise.
theorem cover8_leaf0048_exp_radius : (49907769495583677/50000000000000000 : ℝ) ≤ Real.exp ((-121/8192 : ℝ)/8) ∧ Real.exp ((-121/8192 : ℝ)/8) ≤ (998155389911673541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-121/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0048_exp_lower : (230028608152073223/250000000000000000 : ℝ) ≤ Real.exp ((-666057867233/1000000000000 : ℝ)/8) ∧ Real.exp ((-666057867233/1000000000000 : ℝ)/8) ≤ (920114432608292893/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666057867233/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0048_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410983825799/200000000000 : ℝ) ≤ 4*Real.exp (483/4096 : ℝ)*Real.exp (-mu (radius 8 (121/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (410983825799/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (121/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0048_exp_radius
  have hrNumeric : (12316725513/12500000000 : ℝ) ≤ Real.exp (-121/8192 : ℝ) ∧ Real.exp (-121/8192 : ℝ) ≤ (985338041041/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (12316725513/12500000000 : ℝ) ≤ (radius 8 (121/1024 : ℝ)) ∧ (radius 8 (121/1024 : ℝ)) ≤ (985338041041/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (121/1024 : ℝ)) (12316725513/12500000000 : ℝ) (985338041041/1000000000000 : ℝ) (85306718489/500000000000 : ℝ) (21326679623/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (121/1024 : ℝ)) (12316725513/12500000000 : ℝ) (985338041041/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (121/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (12316725513/12500000000 : ℝ) (985338041041/1000000000000 : ℝ) (24816725513/25000000000 : ℝ) (992669020521/1000000000000 : ℝ) (99264195007/100000000000 : ℝ) (124080243759/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (121/1024 : ℝ)) 1 (24816725513/25000000000 : ℝ) (992669020521/1000000000000 : ℝ) (99264195007/100000000000 : ℝ) (124080243759/125000000000 : ℝ) (198531097059/200000000000 : ℝ) (992655485297/1000000000000 : ℝ) (496327742601/500000000000 : ℝ) (198531097041/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (121/1024 : ℝ)) 2 (198531097059/200000000000 : ℝ) (992655485297/1000000000000 : ℝ) (496327742601/500000000000 : ℝ) (198531097041/200000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (121/1024 : ℝ)) 3 (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (121/1024 : ℝ)) 4 (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (121/1024 : ℝ)) 5 (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (121/1024 : ℝ)) 6 (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (121/1024 : ℝ)) 7 (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (121/1024 : ℝ))) (85306718489/500000000000 : ℝ) (21326679623/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (121/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (85306718489/500000000000 : ℝ) (21326679623/125000000000 : ℝ) (585306718489/1000000000000 : ℝ) (146326679623/250000000000 : ℝ) (41305379429/100000000000 : ℝ) (413053794299/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (121/1024 : ℝ))) 1 (585306718489/1000000000000 : ℝ) (146326679623/250000000000 : ℝ) (41305379429/100000000000 : ℝ) (413053794299/1000000000000 : ℝ) (499180256389/1000000000000 : ℝ) (124795064099/250000000000 : ℝ) (61461771769/125000000000 : ℝ) (491694174159/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (121/1024 : ℝ))) 2 (499180256389/1000000000000 : ℝ) (124795064099/250000000000 : ℝ) (61461771769/125000000000 : ℝ) (491694174159/1000000000000 : ℝ) (49543721527/100000000000 : ℝ) (247718607639/500000000000 : ℝ) (495423075681/1000000000000 : ℝ) (495423075689/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (121/1024 : ℝ))) 3 (49543721527/100000000000 : ℝ) (247718607639/500000000000 : ℝ) (495423075681/1000000000000 : ℝ) (495423075689/1000000000000 : ℝ) (19817205819/40000000000 : ℝ) (123857536371/250000000000 : ℝ) (19817205817/40000000000 : ℝ) (247715072717/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (121/1024 : ℝ))) 4 (19817205819/40000000000 : ℝ) (123857536371/250000000000 : ℝ) (19817205817/40000000000 : ℝ) (247715072717/500000000000 : ℝ) (9908602909/20000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (121/1024 : ℝ))) 5 (9908602909/20000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (121/1024 : ℝ))) 6 (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (121/1024 : ℝ))) 7 (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (121/1024 : ℝ)) hmem 8 (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (121/1024 : ℝ))) hcmem 8 (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (121/1024 : ℝ)) (15510241957/15625000000 : ℝ) (992655485251/1000000000000 : ℝ) (495430145449/1000000000000 : ℝ) (495430145459/1000000000000 : ℝ) (783977789089/1000000000000 : ℝ) (195994447277/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0048_exp_lower
  have heNumeric : (410983825799/200000000000 : ℝ)/4 ≤ Real.exp (-666057867233/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410983825799/200000000000 : ℝ)/4 ≤ Real.exp ((483/4096 : ℝ)-(195994447277/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (483/4096 : ℝ) (121/1024 : ℝ) (195994447277/250000000000 : ℝ) (410983825799/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0049; no trusted numerical premise.
theorem cover8_leaf0049_exp_radius : (998153486083170891/1000000000000000000 : ℝ) ≤ Real.exp ((-969/65536 : ℝ)/8) ∧ Real.exp ((-969/65536 : ℝ)/8) ≤ (249538371520792723/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-969/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0049_exp_lower : (920127719331567687/1000000000000000000 : ℝ) ≤ Real.exp ((-41621396607/62500000000 : ℝ)/8) ∧ Real.exp ((-41621396607/62500000000 : ℝ)/8) ≤ (115015964916445961/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-41621396607/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0049_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205515653009/100000000000 : ℝ) ≤ 4*Real.exp (121/1024 : ℝ)*Real.exp (-mu (radius 8 (969/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (205515653009/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (969/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0049_exp_radius
  have hrNumeric : (985323006089/1000000000000 : ℝ) ≤ Real.exp (-969/65536 : ℝ) ∧ Real.exp (-969/65536 : ℝ) ≤ (98532300609/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (985323006089/1000000000000 : ℝ) ≤ (radius 8 (969/8192 : ℝ)) ∧ (radius 8 (969/8192 : ℝ)) ≤ (98532300609/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (969/8192 : ℝ)) (985323006089/1000000000000 : ℝ) (98532300609/100000000000 : ℝ) (85350122539/500000000000 : ℝ) (42675061271/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (969/8192 : ℝ)) (985323006089/1000000000000 : ℝ) (98532300609/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (969/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (985323006089/1000000000000 : ℝ) (98532300609/100000000000 : ℝ) (248165375761/250000000000 : ℝ) (198532300609/200000000000 : ℝ) (496317188421/500000000000 : ℝ) (992634376843/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (969/8192 : ℝ)) 1 (248165375761/250000000000 : ℝ) (198532300609/200000000000 : ℝ) (496317188421/500000000000 : ℝ) (992634376843/1000000000000 : ℝ) (992647939943/1000000000000 : ℝ) (124080992493/125000000000 : ℝ) (19852958797/20000000000 : ℝ) (248161984963/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (969/8192 : ℝ)) 2 (992647939943/1000000000000 : ℝ) (124080992493/125000000000 : ℝ) (19852958797/20000000000 : ℝ) (248161984963/250000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (969/8192 : ℝ)) 3 (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (969/8192 : ℝ)) 4 (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (969/8192 : ℝ)) 5 (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (969/8192 : ℝ)) 6 (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (969/8192 : ℝ)) 7 (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (969/8192 : ℝ))) (85350122539/500000000000 : ℝ) (42675061271/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (969/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (85350122539/500000000000 : ℝ) (42675061271/250000000000 : ℝ) (585350122539/1000000000000 : ℝ) (292675061271/500000000000 : ℝ) (12911214431/31250000000 : ℝ) (413158861801/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (969/8192 : ℝ))) 1 (585350122539/1000000000000 : ℝ) (292675061271/500000000000 : ℝ) (12911214431/31250000000 : ℝ) (413158861801/1000000000000 : ℝ) (99850898433/200000000000 : ℝ) (124813623043/250000000000 : ℝ) (98354987749/200000000000 : ℝ) (3841991709/7812500000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (969/8192 : ℝ))) 2 (99850898433/200000000000 : ℝ) (124813623043/250000000000 : ℝ) (98354987749/200000000000 : ℝ) (3841991709/7812500000 : ℝ) (99102943091/200000000000 : ℝ) (247757357731/500000000000 : ℝ) (247750301363/500000000000 : ℝ) (247750301367/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (969/8192 : ℝ))) 3 (99102943091/200000000000 : ℝ) (247757357731/500000000000 : ℝ) (247750301363/500000000000 : ℝ) (247750301367/500000000000 : ℝ) (49550765909/100000000000 : ℝ) (247753829549/500000000000 : ℝ) (3096922869/6250000000 : ℝ) (61938457381/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (969/8192 : ℝ))) 4 (49550765909/100000000000 : ℝ) (247753829549/500000000000 : ℝ) (3096922869/6250000000 : ℝ) (61938457381/125000000000 : ℝ) (99101531813/200000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (969/8192 : ℝ))) 5 (99101531813/200000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (969/8192 : ℝ))) 6 (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (969/8192 : ℝ))) 7 (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (969/8192 : ℝ)) hmem 8 (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (969/8192 : ℝ))) hcmem 8 (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (969/8192 : ℝ)) (124080992487/125000000000 : ℝ) (496323969949/500000000000 : ℝ) (61938457383/125000000000 : ℝ) (495507659073/1000000000000 : ℝ) (156821281639/200000000000 : ℝ) (196026602053/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0049_exp_lower
  have heNumeric : (205515653009/100000000000 : ℝ)/4 ≤ Real.exp (-41621396607/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205515653009/100000000000 : ℝ)/4 ≤ Real.exp ((121/1024 : ℝ)-(196026602053/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (121/1024 : ℝ) (969/8192 : ℝ) (196026602053/250000000000 : ℝ) (205515653009/100000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0025_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0025_certificate
#check SmaleRate.Proofs.cover8_leaf0026_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0026_certificate
#check SmaleRate.Proofs.cover8_leaf0027_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0027_certificate
#check SmaleRate.Proofs.cover8_leaf0028_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0028_certificate
#check SmaleRate.Proofs.cover8_leaf0029_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0029_certificate
#check SmaleRate.Proofs.cover8_leaf0030_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0030_certificate
#check SmaleRate.Proofs.cover8_leaf0031_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0031_certificate
#check SmaleRate.Proofs.cover8_leaf0032_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0032_certificate
#check SmaleRate.Proofs.cover8_leaf0033_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0033_certificate
#check SmaleRate.Proofs.cover8_leaf0034_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0034_certificate
#check SmaleRate.Proofs.cover8_leaf0035_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0035_certificate
#check SmaleRate.Proofs.cover8_leaf0036_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0036_certificate
#check SmaleRate.Proofs.cover8_leaf0037_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0037_certificate
#check SmaleRate.Proofs.cover8_leaf0038_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0038_certificate
#check SmaleRate.Proofs.cover8_leaf0039_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0039_certificate
#check SmaleRate.Proofs.cover8_leaf0040_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0040_certificate
#check SmaleRate.Proofs.cover8_leaf0041_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0041_certificate
#check SmaleRate.Proofs.cover8_leaf0042_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0042_certificate
#check SmaleRate.Proofs.cover8_leaf0043_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0043_certificate
#check SmaleRate.Proofs.cover8_leaf0044_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0044_certificate
#check SmaleRate.Proofs.cover8_leaf0045_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0045_certificate
#check SmaleRate.Proofs.cover8_leaf0046_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0046_certificate
#check SmaleRate.Proofs.cover8_leaf0047_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0047_certificate
#check SmaleRate.Proofs.cover8_leaf0048_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0048_certificate
#check SmaleRate.Proofs.cover8_leaf0049_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0049_certificate
