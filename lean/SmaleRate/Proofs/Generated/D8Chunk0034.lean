/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0850; no trusted numerical premise.
theorem cover8_leaf0850_exp_radius : (24950188169855131/25000000000000000 : ℝ) ≤ Real.exp ((-66923/4194304 : ℝ)/8) ∧ Real.exp ((-66923/4194304 : ℝ)/8) ≤ (998007526794205241/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66923/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0850_exp_lower : (92011344773053183/100000000000000000 : ℝ) ≤ Real.exp ((-42628251540923/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251540923/64000000000000 : ℝ)/8) ≤ (920113447730531831/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251540923/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0850_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980306521/200000000000 : ℝ) ≤ 4*Real.exp (33461/262144 : ℝ)*Real.exp (-mu (radius 8 (66923/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980306521/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66923/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0850_exp_radius
  have hrNumeric : (984170931079/1000000000000 : ℝ) ≤ Real.exp (-66923/4194304 : ℝ) ∧ Real.exp (-66923/4194304 : ℝ) ≤ (24604273277/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984170931079/1000000000000 : ℝ) ≤ (radius 8 (66923/524288 : ℝ)) ∧ (radius 8 (66923/524288 : ℝ)) ≤ (24604273277/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66923/524288 : ℝ)) (984170931079/1000000000000 : ℝ) (24604273277/25000000000 : ℝ) (177221833917/1000000000000 : ℝ) (44305458481/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66923/524288 : ℝ)) (984170931079/1000000000000 : ℝ) (24604273277/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66923/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984170931079/1000000000000 : ℝ) (24604273277/25000000000 : ℝ) (992085465539/1000000000000 : ℝ) (49604273277/50000000000 : ℝ) (992053895249/1000000000000 : ℝ) (3968215581/4000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66923/524288 : ℝ)) 1 (992085465539/1000000000000 : ℝ) (49604273277/50000000000 : ℝ) (992053895249/1000000000000 : ℝ) (3968215581/4000000000 : ℝ) (496034840197/500000000000 : ℝ) (198413936079/200000000000 : ℝ) (248017420067/250000000000 : ℝ) (99206968027/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66923/524288 : ℝ)) 2 (496034840197/500000000000 : ℝ) (198413936079/200000000000 : ℝ) (248017420067/250000000000 : ℝ) (99206968027/100000000000 : ℝ) (992069680331/1000000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66923/524288 : ℝ)) 3 (992069680331/1000000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66923/524288 : ℝ)) 4 (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66923/524288 : ℝ)) 5 (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66923/524288 : ℝ)) 6 (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66923/524288 : ℝ)) 7 (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66923/524288 : ℝ))) (177221833917/1000000000000 : ℝ) (44305458481/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66923/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177221833917/1000000000000 : ℝ) (44305458481/250000000000 : ℝ) (294305458479/500000000000 : ℝ) (294305458481/500000000000 : ℝ) (84195447363/200000000000 : ℝ) (16839089473/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66923/524288 : ℝ))) 1 (294305458479/500000000000 : ℝ) (294305458481/500000000000 : ℝ) (84195447363/200000000000 : ℝ) (16839089473/40000000000 : ℝ) (252397038443/500000000000 : ℝ) (252397038447/500000000000 : ℝ) (248893449783/500000000000 : ℝ) (19911475983/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66923/524288 : ℝ))) 2 (252397038443/500000000000 : ℝ) (252397038447/500000000000 : ℝ) (248893449783/500000000000 : ℝ) (19911475983/40000000000 : ℝ) (250645244113/500000000000 : ℝ) (100258097647/200000000000 : ℝ) (501278244543/1000000000000 : ℝ) (62659780569/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66923/524288 : ℝ))) 3 (250645244113/500000000000 : ℝ) (100258097647/200000000000 : ℝ) (501278244543/1000000000000 : ℝ) (62659780569/125000000000 : ℝ) (31330272899/62500000000 : ℝ) (250642183197/500000000000 : ℝ) (501284366347/1000000000000 : ℝ) (501284366357/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66923/524288 : ℝ))) 4 (31330272899/62500000000 : ℝ) (250642183197/500000000000 : ℝ) (501284366347/1000000000000 : ℝ) (501284366357/1000000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66923/524288 : ℝ))) 5 (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66923/524288 : ℝ))) 6 (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66923/524288 : ℝ))) 7 (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66923/524288 : ℝ)) hmem 8 (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66923/524288 : ℝ))) hcmem 8 (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66923/524288 : ℝ)) (99206968033/100000000000 : ℝ) (992069680333/1000000000000 : ℝ) (100256873273/200000000000 : ℝ) (62660545797/125000000000 : ℝ) (793710015511/1000000000000 : ℝ) (198427503883/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0850_exp_lower
  have heNumeric : (410980306521/200000000000 : ℝ)/4 ≤ Real.exp (-42628251540923/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980306521/200000000000 : ℝ)/4 ≤ Real.exp ((33461/262144 : ℝ)-(198427503883/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33461/262144 : ℝ) (66923/524288 : ℝ) (198427503883/250000000000 : ℝ) (410980306521/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0851; no trusted numerical premise.
theorem cover8_leaf0851_exp_radius : (124750937131407953/125000000000000000 : ℝ) ≤ Real.exp ((-16731/1048576 : ℝ)/8) ∧ Real.exp ((-16731/1048576 : ℝ)/8) ≤ (7984059976410109/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16731/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0851_exp_lower : (920113447709096961/1000000000000000000 : ℝ) ≤ Real.exp ((-85256503105701/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503105701/128000000000000 : ℝ)/8) ≤ (460056723854548481/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503105701/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0851_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450766111/500000000000 : ℝ) ≤ 4*Real.exp (66923/524288 : ℝ)*Real.exp (-mu (radius 8 (16731/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450766111/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16731/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0851_exp_radius
  have hrNumeric : (492085348217/500000000000 : ℝ) ≤ Real.exp (-16731/1048576 : ℝ) ∧ Real.exp (-16731/1048576 : ℝ) ≤ (196834139287/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492085348217/500000000000 : ℝ) ≤ (radius 8 (16731/131072 : ℝ)) ∧ (radius 8 (16731/131072 : ℝ)) ≤ (196834139287/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16731/131072 : ℝ)) (492085348217/500000000000 : ℝ) (196834139287/200000000000 : ℝ) (177223136973/1000000000000 : ℝ) (177223136979/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16731/131072 : ℝ)) (492085348217/500000000000 : ℝ) (196834139287/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16731/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492085348217/500000000000 : ℝ) (196834139287/200000000000 : ℝ) (992085348217/1000000000000 : ℝ) (496042674109/500000000000 : ℝ) (496026888493/500000000000 : ℝ) (248013444247/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16731/131072 : ℝ)) 1 (992085348217/1000000000000 : ℝ) (496042674109/500000000000 : ℝ) (496026888493/500000000000 : ℝ) (248013444247/250000000000 : ℝ) (992069562601/1000000000000 : ℝ) (992069562603/1000000000000 : ℝ) (39682782499/40000000000 : ℝ) (496034781239/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16731/131072 : ℝ)) 2 (992069562601/1000000000000 : ℝ) (992069562603/1000000000000 : ℝ) (39682782499/40000000000 : ℝ) (496034781239/500000000000 : ℝ) (496034781269/500000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16731/131072 : ℝ)) 3 (496034781269/500000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16731/131072 : ℝ)) 4 (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16731/131072 : ℝ)) 5 (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16731/131072 : ℝ)) 6 (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16731/131072 : ℝ)) 7 (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16731/131072 : ℝ))) (177223136973/1000000000000 : ℝ) (177223136979/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16731/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177223136973/1000000000000 : ℝ) (177223136979/1000000000000 : ℝ) (294305784243/500000000000 : ℝ) (58861156849/100000000000 : ℝ) (420978784469/1000000000000 : ℝ) (420978784477/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16731/131072 : ℝ))) 1 (294305784243/500000000000 : ℝ) (58861156849/100000000000 : ℝ) (420978784469/1000000000000 : ℝ) (420978784477/1000000000000 : ℝ) (504795176477/1000000000000 : ℝ) (126198794121/250000000000 : ℝ) (3111175563/6250000000 : ℝ) (497788090087/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16731/131072 : ℝ))) 2 (504795176477/1000000000000 : ℝ) (126198794121/250000000000 : ℝ) (3111175563/6250000000 : ℝ) (497788090087/1000000000000 : ℝ) (250645816639/500000000000 : ℝ) (250645816643/500000000000 : ℝ) (501279389941/1000000000000 : ℝ) (501279389949/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16731/131072 : ℝ))) 3 (250645816639/500000000000 : ℝ) (250645816643/500000000000 : ℝ) (501279389941/1000000000000 : ℝ) (501279389949/1000000000000 : ℝ) (501285511609/1000000000000 : ℝ) (250642755809/500000000000 : ℝ) (125321377893/250000000000 : ℝ) (501285511581/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16731/131072 : ℝ))) 4 (501285511609/1000000000000 : ℝ) (250642755809/500000000000 : ℝ) (125321377893/250000000000 : ℝ) (501285511581/1000000000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16731/131072 : ℝ))) 5 (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16731/131072 : ℝ))) 6 (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16731/131072 : ℝ))) 7 (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16731/131072 : ℝ)) hmem 8 (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16731/131072 : ℝ))) hcmem 8 (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16731/131072 : ℝ)) (992069562537/1000000000000 : ℝ) (992069562541/1000000000000 : ℝ) (50128551159/100000000000 : ℝ) (1253213779/2500000000 : ℝ) (793711923047/1000000000000 : ℝ) (793711923067/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0851_exp_lower
  have heNumeric : (1027450766111/500000000000 : ℝ)/4 ≤ Real.exp (-85256503105701/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450766111/500000000000 : ℝ)/4 ≤ Real.exp ((66923/524288 : ℝ)-(793711923067/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66923/524288 : ℝ) (16731/131072 : ℝ) (793711923067/1000000000000 : ℝ) (1027450766111/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0852; no trusted numerical premise.
theorem cover8_leaf0852_exp_radius : (199601493461664579/200000000000000000 : ℝ) ≤ Real.exp ((-66925/4194304 : ℝ)/8) ∧ Real.exp ((-66925/4194304 : ℝ)/8) ≤ (62375466706770181/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66925/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0852_exp_lower : (460056723845498751/500000000000000000 : ℝ) ≤ Real.exp ((-21314125781461/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125781461/32000000000000 : ℝ)/8) ≤ (920113447690997503/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125781461/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0852_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450765949/500000000000 : ℝ) ≤ 4*Real.exp (16731/131072 : ℝ)*Real.exp (-mu (radius 8 (66925/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450765949/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66925/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0852_exp_radius
  have hrNumeric : (98417046179/100000000000 : ℝ) ≤ Real.exp (-66925/4194304 : ℝ) ∧ Real.exp (-66925/4194304 : ℝ) ≤ (984170461791/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98417046179/100000000000 : ℝ) ≤ (radius 8 (66925/524288 : ℝ)) ∧ (radius 8 (66925/524288 : ℝ)) ≤ (984170461791/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66925/524288 : ℝ)) (98417046179/100000000000 : ℝ) (984170461791/1000000000000 : ℝ) (177224440013/1000000000000 : ℝ) (8861222001/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66925/524288 : ℝ)) (98417046179/100000000000 : ℝ) (984170461791/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66925/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98417046179/100000000000 : ℝ) (984170461791/1000000000000 : ℝ) (198417046179/200000000000 : ℝ) (62005326931/62500000000 : ℝ) (39682146349/40000000000 : ℝ) (496026829363/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66925/524288 : ℝ)) 1 (198417046179/200000000000 : ℝ) (62005326931/62500000000 : ℝ) (39682146349/40000000000 : ℝ) (496026829363/500000000000 : ℝ) (99206944481/100000000000 : ℝ) (992069444811/1000000000000 : ℝ) (248017361171/250000000000 : ℝ) (496034722343/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66925/524288 : ℝ)) 2 (99206944481/100000000000 : ℝ) (992069444811/1000000000000 : ℝ) (248017361171/250000000000 : ℝ) (496034722343/500000000000 : ℝ) (992069444747/1000000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66925/524288 : ℝ)) 3 (992069444747/1000000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66925/524288 : ℝ)) 4 (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66925/524288 : ℝ)) 5 (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66925/524288 : ℝ)) 6 (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66925/524288 : ℝ)) 7 (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66925/524288 : ℝ))) (177224440013/1000000000000 : ℝ) (8861222001/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66925/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177224440013/1000000000000 : ℝ) (8861222001/50000000000 : ℝ) (294306110003/500000000000 : ℝ) (58861222001/100000000000 : ℝ) (420980332097/1000000000000 : ℝ) (210490166053/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66925/524288 : ℝ))) 1 (294306110003/500000000000 : ℝ) (58861222001/100000000000 : ℝ) (420980332097/1000000000000 : ℝ) (210490166053/500000000000 : ℝ) (504796276051/1000000000000 : ℝ) (252398138029/500000000000 : ℝ) (248894640287/500000000000 : ℝ) (248894640291/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66925/524288 : ℝ))) 2 (504796276051/1000000000000 : ℝ) (252398138029/500000000000 : ℝ) (248894640287/500000000000 : ℝ) (248894640291/500000000000 : ℝ) (62661597289/125000000000 : ℝ) (6266159729/12500000000 : ℝ) (501280535321/1000000000000 : ℝ) (501280535329/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66925/524288 : ℝ))) 3 (62661597289/125000000000 : ℝ) (6266159729/12500000000 : ℝ) (501280535321/1000000000000 : ℝ) (501280535329/1000000000000 : ℝ) (31330416051/62500000000 : ℝ) (20051466273/40000000000 : ℝ) (501286656779/1000000000000 : ℝ) (125321664197/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66925/524288 : ℝ))) 4 (31330416051/62500000000 : ℝ) (20051466273/40000000000 : ℝ) (501286656779/1000000000000 : ℝ) (125321664197/250000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66925/524288 : ℝ))) 5 (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66925/524288 : ℝ))) 6 (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66925/524288 : ℝ))) 7 (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66925/524288 : ℝ)) hmem 8 (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66925/524288 : ℝ))) hcmem 8 (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66925/524288 : ℝ)) (496034722373/500000000000 : ℝ) (992069444749/1000000000000 : ℝ) (501286656797/1000000000000 : ℝ) (501286656807/1000000000000 : ℝ) (396856915277/500000000000 : ℝ) (793713830573/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0852_exp_lower
  have heNumeric : (1027450765949/500000000000 : ℝ)/4 ≤ Real.exp (-21314125781461/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450765949/500000000000 : ℝ)/4 ≤ Real.exp ((16731/131072 : ℝ)-(793713830573/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16731/131072 : ℝ) (66925/524288 : ℝ) (793713830573/1000000000000 : ℝ) (1027450765949/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0853; no trusted numerical premise.
theorem cover8_leaf0853_exp_radius : (249501859391345763/250000000000000000 : ℝ) ≤ Real.exp ((-33463/2097152 : ℝ)/8) ∧ Real.exp ((-33463/2097152 : ℝ)/8) ≤ (998007437565383053/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33463/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0853_exp_lower : (460056723837024093/500000000000000000 : ℝ) ≤ Real.exp ((-85256503144707/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503144707/128000000000000 : ℝ)/8) ≤ (920113447674048187/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503144707/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0853_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980306319/200000000000 : ℝ) ≤ 4*Real.exp (66925/524288 : ℝ)*Real.exp (-mu (radius 8 (33463/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980306319/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33463/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0853_exp_radius
  have hrNumeric : (196834045429/200000000000 : ℝ) ≤ Real.exp (-33463/2097152 : ℝ) ∧ Real.exp (-33463/2097152 : ℝ) ≤ (492085113573/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196834045429/200000000000 : ℝ) ≤ (radius 8 (33463/262144 : ℝ)) ∧ (radius 8 (33463/262144 : ℝ)) ≤ (492085113573/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33463/262144 : ℝ)) (196834045429/200000000000 : ℝ) (492085113573/500000000000 : ℝ) (177225743049/1000000000000 : ℝ) (35445148611/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33463/262144 : ℝ)) (196834045429/200000000000 : ℝ) (492085113573/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33463/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196834045429/200000000000 : ℝ) (492085113573/500000000000 : ℝ) (248021278393/250000000000 : ℝ) (992085113573/1000000000000 : ℝ) (496026770231/500000000000 : ℝ) (62003346279/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33463/262144 : ℝ)) 1 (248021278393/250000000000 : ℝ) (992085113573/1000000000000 : ℝ) (496026770231/500000000000 : ℝ) (62003346279/62500000000 : ℝ) (992069327017/1000000000000 : ℝ) (992069327019/1000000000000 : ℝ) (992069326891/1000000000000 : ℝ) (992069326893/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33463/262144 : ℝ)) 2 (992069327017/1000000000000 : ℝ) (992069327019/1000000000000 : ℝ) (992069326891/1000000000000 : ℝ) (992069326893/1000000000000 : ℝ) (496034663477/500000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33463/262144 : ℝ)) 3 (496034663477/500000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33463/262144 : ℝ)) 4 (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33463/262144 : ℝ)) 5 (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33463/262144 : ℝ)) 6 (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33463/262144 : ℝ)) 7 (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33463/262144 : ℝ))) (177225743049/1000000000000 : ℝ) (35445148611/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33463/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177225743049/1000000000000 : ℝ) (35445148611/200000000000 : ℝ) (147153217881/250000000000 : ℝ) (73576608941/125000000000 : ℝ) (84196375943/200000000000 : ℝ) (420981879723/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33463/262144 : ℝ))) 1 (147153217881/250000000000 : ℝ) (73576608941/125000000000 : ℝ) (84196375943/200000000000 : ℝ) (420981879723/1000000000000 : ℝ) (504797375619/1000000000000 : ℝ) (252398687813/500000000000 : ℝ) (24889523553/50000000000 : ℝ) (497790471067/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33463/262144 : ℝ))) 2 (504797375619/1000000000000 : ℝ) (252398687813/500000000000 : ℝ) (24889523553/50000000000 : ℝ) (497790471067/1000000000000 : ℝ) (501293923339/1000000000000 : ℝ) (501293923347/1000000000000 : ℝ) (501281680693/1000000000000 : ℝ) (501281680701/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33463/262144 : ℝ))) 3 (501293923339/1000000000000 : ℝ) (501293923347/1000000000000 : ℝ) (501281680693/1000000000000 : ℝ) (501281680701/1000000000000 : ℝ) (15665243813/31250000000 : ℝ) (62660975253/125000000000 : ℝ) (250643900989/500000000000 : ℝ) (501287801987/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33463/262144 : ℝ))) 4 (15665243813/31250000000 : ℝ) (62660975253/125000000000 : ℝ) (250643900989/500000000000 : ℝ) (501287801987/1000000000000 : ℝ) (501287801997/1000000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33463/262144 : ℝ))) 5 (501287801997/1000000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33463/262144 : ℝ))) 6 (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33463/262144 : ℝ))) 7 (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33463/262144 : ℝ)) hmem 8 (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33463/262144 : ℝ))) hcmem 8 (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33463/262144 : ℝ)) (992069326953/1000000000000 : ℝ) (248017331739/250000000000 : ℝ) (125321950499/250000000000 : ℝ) (250643901003/500000000000 : ℝ) (15874314761/20000000000 : ℝ) (793715738069/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0853_exp_lower
  have heNumeric : (410980306319/200000000000 : ℝ)/4 ≤ Real.exp (-85256503144707/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980306319/200000000000 : ℝ)/4 ≤ Real.exp ((66925/524288 : ℝ)-(793715738069/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66925/524288 : ℝ) (33463/262144 : ℝ) (793715738069/1000000000000 : ℝ) (410980306319/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0854; no trusted numerical premise.
theorem cover8_leaf0854_exp_radius : (15593865747225689/15625000000000000 : ℝ) ≤ Real.exp ((-66927/4194304 : ℝ)/8) ∧ Real.exp ((-66927/4194304 : ℝ)/8) ≤ (998007407822444097/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66927/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0854_exp_lower : (92011344765985921/100000000000000000 : ℝ) ≤ Real.exp ((-42628251580249/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251580249/64000000000000 : ℝ)/8) ≤ (920113447659859211/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251580249/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0854_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450765671/500000000000 : ℝ) ≤ 4*Real.exp (33463/262144 : ℝ)*Real.exp (-mu (radius 8 (66927/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450765671/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66927/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0854_exp_radius
  have hrNumeric : (984169992501/1000000000000 : ℝ) ≤ Real.exp (-66927/4194304 : ℝ) ∧ Real.exp (-66927/4194304 : ℝ) ≤ (492084996251/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984169992501/1000000000000 : ℝ) ≤ (radius 8 (66927/524288 : ℝ)) ∧ (radius 8 (66927/524288 : ℝ)) ≤ (492084996251/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66927/524288 : ℝ)) (984169992501/1000000000000 : ℝ) (492084996251/500000000000 : ℝ) (177227046069/1000000000000 : ℝ) (44306761519/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66927/524288 : ℝ)) (984169992501/1000000000000 : ℝ) (492084996251/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66927/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984169992501/1000000000000 : ℝ) (492084996251/500000000000 : ℝ) (793667997/800000000 : ℝ) (992084996251/1000000000000 : ℝ) (992053422201/1000000000000 : ℝ) (496026711101/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66927/524288 : ℝ)) 1 (793667997/800000000 : ℝ) (992084996251/1000000000000 : ℝ) (992053422201/1000000000000 : ℝ) (496026711101/500000000000 : ℝ) (39682768369/40000000000 : ℝ) (992069209227/1000000000000 : ℝ) (992069209099/1000000000000 : ℝ) (992069209101/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66927/524288 : ℝ)) 2 (39682768369/40000000000 : ℝ) (992069209227/1000000000000 : ℝ) (992069209099/1000000000000 : ℝ) (992069209101/1000000000000 : ℝ) (496034604581/500000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66927/524288 : ℝ)) 3 (496034604581/500000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66927/524288 : ℝ)) 4 (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66927/524288 : ℝ)) 5 (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66927/524288 : ℝ)) 6 (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66927/524288 : ℝ)) 7 (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66927/524288 : ℝ))) (177227046069/1000000000000 : ℝ) (44306761519/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66927/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177227046069/1000000000000 : ℝ) (44306761519/250000000000 : ℝ) (294306761517/500000000000 : ℝ) (294306761519/500000000000 : ℝ) (420983427309/1000000000000 : ℝ) (210491713659/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66927/524288 : ℝ))) 1 (294306761517/500000000000 : ℝ) (294306761519/500000000000 : ℝ) (420983427309/1000000000000 : ℝ) (210491713659/500000000000 : ℝ) (504798475171/1000000000000 : ℝ) (252399237589/500000000000 : ℝ) (62223957691/125000000000 : ℝ) (15555989423/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66927/524288 : ℝ))) 2 (504798475171/1000000000000 : ℝ) (252399237589/500000000000 : ℝ) (62223957691/125000000000 : ℝ) (15555989423/31250000000 : ℝ) (501295068349/1000000000000 : ℝ) (501295068357/1000000000000 : ℝ) (501282826049/1000000000000 : ℝ) (250641413029/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66927/524288 : ℝ))) 3 (501295068349/1000000000000 : ℝ) (501295068357/1000000000000 : ℝ) (501282826049/1000000000000 : ℝ) (250641413029/500000000000 : ℝ) (501288947199/1000000000000 : ℝ) (62661118401/125000000000 : ℝ) (501288947161/1000000000000 : ℝ) (501288947171/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66927/524288 : ℝ))) 4 (501288947199/1000000000000 : ℝ) (62661118401/125000000000 : ℝ) (501288947161/1000000000000 : ℝ) (501288947171/1000000000000 : ℝ) (25064447359/50000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66927/524288 : ℝ))) 5 (25064447359/50000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66927/524288 : ℝ))) 6 (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66927/524288 : ℝ))) 7 (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66927/524288 : ℝ)) hmem 8 (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66927/524288 : ℝ))) hcmem 8 (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66927/524288 : ℝ)) (992069209161/1000000000000 : ℝ) (248017302291/250000000000 : ℝ) (501288947179/1000000000000 : ℝ) (50128894719/100000000000 : ℝ) (793717645521/1000000000000 : ℝ) (793717645541/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0854_exp_lower
  have heNumeric : (1027450765671/500000000000 : ℝ)/4 ≤ Real.exp (-42628251580249/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450765671/500000000000 : ℝ)/4 ≤ Real.exp ((33463/262144 : ℝ)-(793717645541/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33463/262144 : ℝ) (66927/524288 : ℝ) (793717645541/1000000000000 : ℝ) (1027450765671/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0855; no trusted numerical premise.
theorem cover8_leaf0855_exp_radius : (39920295123180241/40000000000000000 : ℝ) ≤ Real.exp ((-4183/262144 : ℝ)/8) ∧ Real.exp ((-4183/262144 : ℝ)/8) ≤ (499003689039753013/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4183/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0855_exp_lower : (460056723823582709/500000000000000000 : ℝ) ≤ Real.exp ((-682052025397/1024000000000 : ℝ)/8) ∧ Real.exp ((-682052025397/1024000000000 : ℝ)/8) ≤ (920113447647165419/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682052025397/1024000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0855_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980306223/200000000000 : ℝ) ≤ 4*Real.exp (66927/524288 : ℝ)*Real.exp (-mu (radius 8 (4183/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (410980306223/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4183/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0855_exp_radius
  have hrNumeric : (30755304933/31250000000 : ℝ) ≤ Real.exp (-4183/262144 : ℝ) ∧ Real.exp (-4183/262144 : ℝ) ≤ (984169757857/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30755304933/31250000000 : ℝ) ≤ (radius 8 (4183/32768 : ℝ)) ∧ (radius 8 (4183/32768 : ℝ)) ≤ (984169757857/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4183/32768 : ℝ)) (30755304933/31250000000 : ℝ) (984169757857/1000000000000 : ℝ) (35445669817/200000000000 : ℝ) (44307087273/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4183/32768 : ℝ)) (30755304933/31250000000 : ℝ) (984169757857/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4183/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30755304933/31250000000 : ℝ) (984169757857/1000000000000 : ℝ) (62005304933/62500000000 : ℝ) (992084878929/1000000000000 : ℝ) (496026651969/500000000000 : ℝ) (49602665197/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4183/32768 : ℝ)) 1 (62005304933/62500000000 : ℝ) (992084878929/1000000000000 : ℝ) (496026651969/500000000000 : ℝ) (49602665197/50000000000 : ℝ) (992069091433/1000000000000 : ℝ) (198413818287/200000000000 : ℝ) (992069091307/1000000000000 : ℝ) (992069091309/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4183/32768 : ℝ)) 2 (992069091433/1000000000000 : ℝ) (198413818287/200000000000 : ℝ) (992069091307/1000000000000 : ℝ) (992069091309/1000000000000 : ℝ) (99206909137/100000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4183/32768 : ℝ)) 3 (99206909137/100000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4183/32768 : ℝ)) 4 (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4183/32768 : ℝ)) 5 (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4183/32768 : ℝ)) 6 (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4183/32768 : ℝ)) 7 (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4183/32768 : ℝ))) (35445669817/200000000000 : ℝ) (44307087273/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4183/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35445669817/200000000000 : ℝ) (44307087273/250000000000 : ℝ) (294307087271/500000000000 : ℝ) (294307087273/500000000000 : ℝ) (105246243723/250000000000 : ℝ) (420984974901/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4183/32768 : ℝ))) 1 (294307087271/500000000000 : ℝ) (294307087273/500000000000 : ℝ) (105246243723/250000000000 : ℝ) (420984974901/1000000000000 : ℝ) (504799574717/1000000000000 : ℝ) (126199893681/250000000000 : ℝ) (124448212997/250000000000 : ℝ) (124448212999/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4183/32768 : ℝ))) 2 (504799574717/1000000000000 : ℝ) (126199893681/250000000000 : ℝ) (124448212997/250000000000 : ℝ) (124448212999/250000000000 : ℝ) (62662026669/125000000000 : ℝ) (6266202667/12500000000 : ℝ) (250641985699/500000000000 : ℝ) (250641985703/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4183/32768 : ℝ))) 3 (62662026669/125000000000 : ℝ) (6266202667/12500000000 : ℝ) (250641985699/500000000000 : ℝ) (250641985703/500000000000 : ℝ) (4010320739/8000000000 : ℝ) (501290092383/1000000000000 : ℝ) (501290092337/1000000000000 : ℝ) (250645046173/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4183/32768 : ℝ))) 4 (4010320739/8000000000 : ℝ) (501290092383/1000000000000 : ℝ) (501290092337/1000000000000 : ℝ) (250645046173/500000000000 : ℝ) (125322523089/250000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4183/32768 : ℝ))) 5 (125322523089/250000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4183/32768 : ℝ))) 6 (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4183/32768 : ℝ))) 7 (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4183/32768 : ℝ)) hmem 8 (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4183/32768 : ℝ))) hcmem 8 (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4183/32768 : ℝ)) (992069091369/1000000000000 : ℝ) (248017272843/250000000000 : ℝ) (100258018471/200000000000 : ℝ) (100258018473/200000000000 : ℝ) (39685977649/50000000000 : ℝ) (793719553/1000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0855_exp_lower
  have heNumeric : (410980306223/200000000000 : ℝ)/4 ≤ Real.exp (-682052025397/1024000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980306223/200000000000 : ℝ)/4 ≤ Real.exp ((66927/524288 : ℝ)-(793719553/1000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66927/524288 : ℝ) (4183/32768 : ℝ) (793719553/1000000000 : ℝ) (410980306223/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0856; no trusted numerical premise.
theorem cover8_leaf0856_exp_radius : (499003674168284421/500000000000000000 : ℝ) ≤ Real.exp ((-66929/4194304 : ℝ)/8) ∧ Real.exp ((-66929/4194304 : ℝ)/8) ≤ (998007348336568843/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66929/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0856_exp_lower : (184022689527492399/200000000000000000 : ℝ) ≤ Real.exp ((-5328531449089/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328531449089/8000000000000 : ℝ)/8) ≤ (230028361909365499/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328531449089/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0856_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450765471/500000000000 : ℝ) ≤ 4*Real.exp (4183/32768 : ℝ)*Real.exp (-mu (radius 8 (66929/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450765471/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66929/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0856_exp_radius
  have hrNumeric : (246042380803/250000000000 : ℝ) ≤ Real.exp (-66929/4194304 : ℝ) ∧ Real.exp (-66929/4194304 : ℝ) ≤ (984169523213/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246042380803/250000000000 : ℝ) ≤ (radius 8 (66929/524288 : ℝ)) ∧ (radius 8 (66929/524288 : ℝ)) ≤ (984169523213/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66929/524288 : ℝ)) (246042380803/250000000000 : ℝ) (984169523213/1000000000000 : ℝ) (88614826043/500000000000 : ℝ) (177229652093/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66929/524288 : ℝ)) (246042380803/250000000000 : ℝ) (984169523213/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66929/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246042380803/250000000000 : ℝ) (984169523213/1000000000000 : ℝ) (496042380803/500000000000 : ℝ) (992084761607/1000000000000 : ℝ) (992053185677/1000000000000 : ℝ) (496026592839/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66929/524288 : ℝ)) 1 (496042380803/500000000000 : ℝ) (992084761607/1000000000000 : ℝ) (992053185677/1000000000000 : ℝ) (496026592839/500000000000 : ℝ) (992068973641/1000000000000 : ℝ) (992068973643/1000000000000 : ℝ) (198413794703/200000000000 : ℝ) (992068973517/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66929/524288 : ℝ)) 2 (992068973641/1000000000000 : ℝ) (992068973643/1000000000000 : ℝ) (198413794703/200000000000 : ℝ) (992068973517/1000000000000 : ℝ) (496034486789/500000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66929/524288 : ℝ)) 3 (496034486789/500000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66929/524288 : ℝ)) 4 (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66929/524288 : ℝ)) 5 (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66929/524288 : ℝ)) 6 (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66929/524288 : ℝ)) 7 (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66929/524288 : ℝ))) (88614826043/500000000000 : ℝ) (177229652093/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66929/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88614826043/500000000000 : ℝ) (177229652093/1000000000000 : ℝ) (588614826043/1000000000000 : ℝ) (588614826047/1000000000000 : ℝ) (420986522451/1000000000000 : ℝ) (420986522461/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66929/524288 : ℝ))) 1 (588614826043/1000000000000 : ℝ) (588614826047/1000000000000 : ℝ) (420986522451/1000000000000 : ℝ) (420986522461/1000000000000 : ℝ) (504800674247/1000000000000 : ℝ) (252400337127/500000000000 : ℝ) (49779404243/100000000000 : ℝ) (248897021219/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66929/524288 : ℝ))) 2 (504800674247/1000000000000 : ℝ) (252400337127/500000000000 : ℝ) (49779404243/100000000000 : ℝ) (248897021219/500000000000 : ℝ) (250648679169/500000000000 : ℝ) (250648679173/500000000000 : ℝ) (501285116729/1000000000000 : ℝ) (250642558369/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66929/524288 : ℝ))) 3 (250648679169/500000000000 : ℝ) (250648679173/500000000000 : ℝ) (501285116729/1000000000000 : ℝ) (250642558369/500000000000 : ℝ) (501291237533/1000000000000 : ℝ) (250645618771/500000000000 : ℝ) (62661404687/125000000000 : ℝ) (100258247501/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66929/524288 : ℝ))) 4 (501291237533/1000000000000 : ℝ) (250645618771/500000000000 : ℝ) (62661404687/125000000000 : ℝ) (100258247501/200000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66929/524288 : ℝ))) 5 (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66929/524288 : ℝ))) 6 (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66929/524288 : ℝ))) 7 (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66929/524288 : ℝ)) hmem 8 (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66929/524288 : ℝ))) hcmem 8 (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66929/524288 : ℝ)) (992068973577/1000000000000 : ℝ) (49603448679/50000000000 : ℝ) (250645618757/500000000000 : ℝ) (125322809381/250000000000 : ℝ) (396860730207/500000000000 : ℝ) (793721460433/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0856_exp_lower
  have heNumeric : (1027450765471/500000000000 : ℝ)/4 ≤ Real.exp (-5328531449089/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450765471/500000000000 : ℝ)/4 ≤ Real.exp ((4183/32768 : ℝ)-(793721460433/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4183/32768 : ℝ) (66929/524288 : ℝ) (793721460433/1000000000000 : ℝ) (1027450765471/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0857; no trusted numerical premise.
theorem cover8_leaf0857_exp_radius : (199601463718726509/200000000000000000 : ℝ) ≤ Real.exp ((-33465/2097152 : ℝ)/8) ∧ Real.exp ((-33465/2097152 : ℝ)/8) ≤ (499003659296816273/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33465/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0857_exp_lower : (115014180953757357/125000000000000000 : ℝ) ≤ Real.exp ((-85256503193663/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503193663/128000000000000 : ℝ)/8) ≤ (920113447630058857/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503193663/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0857_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490153081/100000000000 : ℝ) ≤ 4*Real.exp (66929/524288 : ℝ)*Real.exp (-mu (radius 8 (33465/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490153081/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33465/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0857_exp_radius
  have hrNumeric : (123021161071/125000000000 : ℝ) ≤ Real.exp (-33465/2097152 : ℝ) ∧ Real.exp (-33465/2097152 : ℝ) ≤ (984169288569/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123021161071/125000000000 : ℝ) ≤ (radius 8 (33465/262144 : ℝ)) ∧ (radius 8 (33465/262144 : ℝ)) ≤ (984169288569/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33465/262144 : ℝ)) (123021161071/125000000000 : ℝ) (984169288569/1000000000000 : ℝ) (177230955077/1000000000000 : ℝ) (177230955083/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33465/262144 : ℝ)) (123021161071/125000000000 : ℝ) (984169288569/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33465/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123021161071/125000000000 : ℝ) (984169288569/1000000000000 : ℝ) (248021161071/250000000000 : ℝ) (198416928857/200000000000 : ℝ) (198410613483/200000000000 : ℝ) (124006633427/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33465/262144 : ℝ)) 1 (248021161071/250000000000 : ℝ) (198416928857/200000000000 : ℝ) (198410613483/200000000000 : ℝ) (124006633427/125000000000 : ℝ) (992068855849/1000000000000 : ℝ) (992068855851/1000000000000 : ℝ) (992068855723/1000000000000 : ℝ) (39682754229/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33465/262144 : ℝ)) 2 (992068855849/1000000000000 : ℝ) (992068855851/1000000000000 : ℝ) (992068855723/1000000000000 : ℝ) (39682754229/40000000000 : ℝ) (496034427893/500000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33465/262144 : ℝ)) 3 (496034427893/500000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33465/262144 : ℝ)) 4 (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33465/262144 : ℝ)) 5 (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33465/262144 : ℝ)) 6 (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33465/262144 : ℝ)) 7 (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33465/262144 : ℝ))) (177230955077/1000000000000 : ℝ) (177230955083/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33465/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177230955077/1000000000000 : ℝ) (177230955083/1000000000000 : ℝ) (294307738769/500000000000 : ℝ) (294307738771/500000000000 : ℝ) (420988069993/1000000000000 : ℝ) (420988070001/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33465/262144 : ℝ))) 1 (294307738769/500000000000 : ℝ) (294307738771/500000000000 : ℝ) (420988069993/1000000000000 : ℝ) (420988070001/1000000000000 : ℝ) (100960354753/200000000000 : ℝ) (126200443443/250000000000 : ℝ) (248897616429/500000000000 : ℝ) (248897616433/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33465/262144 : ℝ))) 2 (100960354753/200000000000 : ℝ) (126200443443/250000000000 : ℝ) (248897616429/500000000000 : ℝ) (248897616433/500000000000 : ℝ) (501298503311/1000000000000 : ℝ) (501298503319/1000000000000 : ℝ) (15665195689/31250000000 : ℝ) (62660782757/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33465/262144 : ℝ))) 3 (501298503311/1000000000000 : ℝ) (501298503319/1000000000000 : ℝ) (15665195689/31250000000 : ℝ) (62660782757/125000000000 : ℝ) (501292382679/1000000000000 : ℝ) (15665386959/31250000000 : ℝ) (250646191321/500000000000 : ℝ) (501292382651/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33465/262144 : ℝ))) 4 (501292382679/1000000000000 : ℝ) (15665386959/31250000000 : ℝ) (250646191321/500000000000 : ℝ) (501292382651/1000000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33465/262144 : ℝ))) 5 (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33465/262144 : ℝ))) 6 (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33465/262144 : ℝ))) 7 (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33465/262144 : ℝ)) hmem 8 (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33465/262144 : ℝ))) hcmem 8 (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33465/262144 : ℝ)) (198413771157/200000000000 : ℝ) (248017213947/250000000000 : ℝ) (25064619133/50000000000 : ℝ) (50129238267/100000000000 : ℝ) (793723367827/1000000000000 : ℝ) (396861683923/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0857_exp_lower
  have heNumeric : (205490153081/100000000000 : ℝ)/4 ≤ Real.exp (-85256503193663/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490153081/100000000000 : ℝ)/4 ≤ Real.exp ((66929/524288 : ℝ)-(396861683923/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66929/524288 : ℝ) (33465/262144 : ℝ) (396861683923/500000000000 : ℝ) (205490153081/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0858; no trusted numerical premise.
theorem cover8_leaf0858_exp_radius : (499003644425348567/500000000000000000 : ℝ) ≤ Real.exp ((-66931/4194304 : ℝ)/8) ∧ Real.exp ((-66931/4194304 : ℝ)/8) ≤ (199601457770139427/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66931/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0858_exp_lower : (230028361906181493/250000000000000000 : ℝ) ≤ Real.exp ((-42628251599799/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251599799/64000000000000 : ℝ)/8) ≤ (920113447624725973/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251599799/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0858_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450765357/500000000000 : ℝ) ≤ 4*Real.exp (33465/262144 : ℝ)*Real.exp (-mu (radius 8 (66931/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450765357/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66931/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0858_exp_radius
  have hrNumeric : (246042263481/250000000000 : ℝ) ≤ Real.exp (-66931/4194304 : ℝ) ∧ Real.exp (-66931/4194304 : ℝ) ≤ (39366762157/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246042263481/250000000000 : ℝ) ≤ (radius 8 (66931/524288 : ℝ)) ∧ (radius 8 (66931/524288 : ℝ)) ≤ (39366762157/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66931/524288 : ℝ)) (246042263481/250000000000 : ℝ) (39366762157/40000000000 : ℝ) (88616129029/500000000000 : ℝ) (11077016129/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66931/524288 : ℝ)) (246042263481/250000000000 : ℝ) (39366762157/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66931/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246042263481/250000000000 : ℝ) (39366762157/40000000000 : ℝ) (496042263481/500000000000 : ℝ) (992084526963/1000000000000 : ℝ) (992052949153/1000000000000 : ℝ) (496026474577/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66931/524288 : ℝ)) 1 (496042263481/500000000000 : ℝ) (992084526963/1000000000000 : ℝ) (992052949153/1000000000000 : ℝ) (496026474577/500000000000 : ℝ) (992068738057/1000000000000 : ℝ) (992068738059/1000000000000 : ℝ) (992068737931/1000000000000 : ℝ) (992068737933/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66931/524288 : ℝ)) 2 (992068738057/1000000000000 : ℝ) (992068738059/1000000000000 : ℝ) (992068737931/1000000000000 : ℝ) (992068737933/1000000000000 : ℝ) (496034368997/500000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66931/524288 : ℝ)) 3 (496034368997/500000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66931/524288 : ℝ)) 4 (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66931/524288 : ℝ)) 5 (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66931/524288 : ℝ)) 6 (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66931/524288 : ℝ)) 7 (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66931/524288 : ℝ))) (88616129029/500000000000 : ℝ) (11077016129/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66931/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88616129029/500000000000 : ℝ) (11077016129/62500000000 : ℝ) (588616129029/1000000000000 : ℝ) (73577016129/125000000000 : ℝ) (210494808759/500000000000 : ℝ) (210494808763/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66931/524288 : ℝ))) 1 (588616129029/1000000000000 : ℝ) (73577016129/125000000000 : ℝ) (210494808759/500000000000 : ℝ) (210494808763/500000000000 : ℝ) (504802873273/1000000000000 : ℝ) (504802873279/1000000000000 : ℝ) (248898211637/500000000000 : ℝ) (497796423281/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66931/524288 : ℝ))) 2 (504802873273/1000000000000 : ℝ) (504802873279/1000000000000 : ℝ) (248898211637/500000000000 : ℝ) (497796423281/1000000000000 : ℝ) (501299648273/1000000000000 : ℝ) (12532491207/25000000000 : ℝ) (125321851839/250000000000 : ℝ) (501287407363/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66931/524288 : ℝ))) 3 (501299648273/1000000000000 : ℝ) (12532491207/25000000000 : ℝ) (125321851839/250000000000 : ℝ) (501287407363/1000000000000 : ℝ) (250646763907/500000000000 : ℝ) (250646763911/500000000000 : ℝ) (501293527777/1000000000000 : ℝ) (100258705557/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66931/524288 : ℝ))) 4 (250646763907/500000000000 : ℝ) (250646763911/500000000000 : ℝ) (501293527777/1000000000000 : ℝ) (100258705557/200000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66931/524288 : ℝ))) 5 (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66931/524288 : ℝ))) 6 (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66931/524288 : ℝ))) 7 (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66931/524288 : ℝ)) hmem 8 (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66931/524288 : ℝ))) hcmem 8 (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66931/524288 : ℝ)) (992068737993/1000000000000 : ℝ) (248017184499/250000000000 : ℝ) (100258705559/200000000000 : ℝ) (125323381951/250000000000 : ℝ) (793725275223/1000000000000 : ℝ) (793725275241/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0858_exp_lower
  have heNumeric : (1027450765357/500000000000 : ℝ)/4 ≤ Real.exp (-42628251599799/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450765357/500000000000 : ℝ)/4 ≤ Real.exp ((33465/262144 : ℝ)-(793725275241/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33465/262144 : ℝ) (66931/524288 : ℝ) (793725275241/1000000000000 : ℝ) (1027450765357/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0859; no trusted numerical premise.
theorem cover8_leaf0859_exp_radius : (998007259107762609/1000000000000000000 : ℝ) ≤ Real.exp ((-16733/1048576 : ℝ)/8) ∧ Real.exp ((-16733/1048576 : ℝ)/8) ≤ (99800725910776261/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16733/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0859_exp_lower : (92011344762054323/100000000000000000 : ℝ) ≤ Real.exp ((-85256503204253/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503204253/128000000000000 : ℝ)/8) ≤ (920113447620543231/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503204253/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0859_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686269133/12500000000 : ℝ) ≤ 4*Real.exp (66931/524288 : ℝ)*Real.exp (-mu (radius 8 (16733/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (25686269133/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16733/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0859_exp_radius
  have hrNumeric : (984168819279/1000000000000 : ℝ) ≤ Real.exp (-16733/1048576 : ℝ) ∧ Real.exp (-16733/1048576 : ℝ) ≤ (12302110241/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984168819279/1000000000000 : ℝ) ≤ (radius 8 (16733/131072 : ℝ)) ∧ (radius 8 (16733/131072 : ℝ)) ≤ (12302110241/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16733/131072 : ℝ)) (984168819279/1000000000000 : ℝ) (12302110241/12500000000 : ℝ) (88616780517/500000000000 : ℝ) (177233561041/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16733/131072 : ℝ)) (984168819279/1000000000000 : ℝ) (12302110241/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16733/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984168819279/1000000000000 : ℝ) (12302110241/12500000000 : ℝ) (992084409639/1000000000000 : ℝ) (24802110241/25000000000 : ℝ) (992052830891/1000000000000 : ℝ) (248013207723/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16733/131072 : ℝ)) 1 (992084409639/1000000000000 : ℝ) (24802110241/25000000000 : ℝ) (992052830891/1000000000000 : ℝ) (248013207723/250000000000 : ℝ) (198413724053/200000000000 : ℝ) (496034310133/500000000000 : ℝ) (992068620139/1000000000000 : ℝ) (992068620141/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16733/131072 : ℝ)) 2 (198413724053/200000000000 : ℝ) (496034310133/500000000000 : ℝ) (992068620139/1000000000000 : ℝ) (992068620141/1000000000000 : ℝ) (496034310101/500000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16733/131072 : ℝ)) 3 (496034310101/500000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16733/131072 : ℝ)) 4 (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16733/131072 : ℝ)) 5 (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16733/131072 : ℝ)) 6 (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16733/131072 : ℝ)) 7 (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16733/131072 : ℝ))) (88616780517/500000000000 : ℝ) (177233561041/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16733/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88616780517/500000000000 : ℝ) (177233561041/1000000000000 : ℝ) (588616780517/1000000000000 : ℝ) (588616780521/1000000000000 : ℝ) (42099116503/100000000000 : ℝ) (5262389563/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16733/131072 : ℝ))) 1 (588616780517/1000000000000 : ℝ) (588616780521/1000000000000 : ℝ) (42099116503/100000000000 : ℝ) (5262389563/12500000000 : ℝ) (504803972773/1000000000000 : ℝ) (504803972781/1000000000000 : ℝ) (6222470171/12500000000 : ℝ) (497797613689/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16733/131072 : ℝ))) 2 (504803972773/1000000000000 : ℝ) (504803972781/1000000000000 : ℝ) (6222470171/12500000000 : ℝ) (497797613689/1000000000000 : ℝ) (250650396613/500000000000 : ℝ) (100260158647/200000000000 : ℝ) (250644276327/500000000000 : ℝ) (62661069083/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16733/131072 : ℝ))) 3 (250650396613/500000000000 : ℝ) (100260158647/200000000000 : ℝ) (250644276327/500000000000 : ℝ) (62661069083/125000000000 : ℝ) (25064733647/50000000000 : ℝ) (10025893459/20000000000 : ℝ) (250647336451/500000000000 : ℝ) (501294672913/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16733/131072 : ℝ))) 4 (25064733647/50000000000 : ℝ) (10025893459/20000000000 : ℝ) (250647336451/500000000000 : ℝ) (501294672913/1000000000000 : ℝ) (501294672921/1000000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16733/131072 : ℝ))) 5 (501294672921/1000000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16733/131072 : ℝ))) 6 (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16733/131072 : ℝ))) 7 (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16733/131072 : ℝ)) hmem 8 (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16733/131072 : ℝ))) hcmem 8 (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16733/131072 : ℝ)) (992068620201/1000000000000 : ℝ) (248017155051/250000000000 : ℝ) (12532366823/25000000000 : ℝ) (125323668233/250000000000 : ℝ) (198431795651/250000000000 : ℝ) (396863591313/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0859_exp_lower
  have heNumeric : (25686269133/12500000000 : ℝ)/4 ≤ Real.exp (-85256503204253/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686269133/12500000000 : ℝ)/4 ≤ Real.exp ((66931/524288 : ℝ)-(396863591313/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66931/524288 : ℝ) (16733/131072 : ℝ) (396863591313/500000000000 : ℝ) (25686269133/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0860; no trusted numerical premise.
theorem cover8_leaf0860_exp_radius : (998007229364828971/1000000000000000000 : ℝ) ≤ Real.exp ((-66933/4194304 : ℝ)/8) ∧ Real.exp ((-66933/4194304 : ℝ)/8) ≤ (249501807341207243/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66933/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0860_exp_lower : (920113447619925927/1000000000000000000 : ℝ) ≤ Real.exp ((-4262825160247/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262825160247/6400000000000 : ℝ)/8) ≤ (115014180952490741/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262825160247/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0860_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901530629/1000000000000 : ℝ) ≤ 4*Real.exp (16733/131072 : ℝ)*Real.exp (-mu (radius 8 (66933/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901530629/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66933/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0860_exp_radius
  have hrNumeric : (196833716927/200000000000 : ℝ) ≤ Real.exp (-66933/4194304 : ℝ) ∧ Real.exp (-66933/4194304 : ℝ) ≤ (246042146159/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196833716927/200000000000 : ℝ) ≤ (radius 8 (66933/524288 : ℝ)) ∧ (radius 8 (66933/524288 : ℝ)) ≤ (246042146159/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66933/524288 : ℝ)) (196833716927/200000000000 : ℝ) (246042146159/250000000000 : ℝ) (35446972799/200000000000 : ℝ) (88617432001/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66933/524288 : ℝ)) (196833716927/200000000000 : ℝ) (246042146159/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66933/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196833716927/200000000000 : ℝ) (246042146159/250000000000 : ℝ) (992084292317/1000000000000 : ℝ) (496042146159/500000000000 : ℝ) (992052712629/1000000000000 : ℝ) (99205271263/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66933/524288 : ℝ)) 1 (992084292317/1000000000000 : ℝ) (496042146159/500000000000 : ℝ) (992052712629/1000000000000 : ℝ) (99205271263/100000000000 : ℝ) (992068502473/1000000000000 : ℝ) (496034251237/500000000000 : ℝ) (992068502347/1000000000000 : ℝ) (992068502349/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66933/524288 : ℝ)) 2 (992068502473/1000000000000 : ℝ) (496034251237/500000000000 : ℝ) (992068502347/1000000000000 : ℝ) (992068502349/1000000000000 : ℝ) (99206850241/100000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66933/524288 : ℝ)) 3 (99206850241/100000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66933/524288 : ℝ)) 4 (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66933/524288 : ℝ)) 5 (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66933/524288 : ℝ)) 6 (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66933/524288 : ℝ)) 7 (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66933/524288 : ℝ))) (35446972799/200000000000 : ℝ) (88617432001/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66933/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35446972799/200000000000 : ℝ) (88617432001/500000000000 : ℝ) (588617431997/1000000000000 : ℝ) (588617432001/1000000000000 : ℝ) (10524817813/25000000000 : ℝ) (420992712529/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66933/524288 : ℝ))) 1 (588617431997/1000000000000 : ℝ) (588617432001/1000000000000 : ℝ) (10524817813/25000000000 : ℝ) (420992712529/1000000000000 : ℝ) (252402536129/500000000000 : ℝ) (100961014453/200000000000 : ℝ) (497798804069/1000000000000 : ℝ) (497798804077/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66933/524288 : ℝ))) 2 (252402536129/500000000000 : ℝ) (100961014453/200000000000 : ℝ) (497798804069/1000000000000 : ℝ) (497798804077/1000000000000 : ℝ) (501301938163/1000000000000 : ℝ) (501301938171/1000000000000 : ℝ) (501289697937/1000000000000 : ℝ) (100257939589/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66933/524288 : ℝ))) 3 (501301938163/1000000000000 : ℝ) (501301938171/1000000000000 : ℝ) (501289697937/1000000000000 : ℝ) (100257939589/200000000000 : ℝ) (10025916361/20000000000 : ℝ) (250647909029/500000000000 : ℝ) (125323954503/250000000000 : ℝ) (501295818021/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66933/524288 : ℝ))) 4 (10025916361/20000000000 : ℝ) (250647909029/500000000000 : ℝ) (125323954503/250000000000 : ℝ) (501295818021/1000000000000 : ℝ) (501295818031/1000000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66933/524288 : ℝ))) 5 (501295818031/1000000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66933/524288 : ℝ))) 6 (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66933/524288 : ℝ))) 7 (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66933/524288 : ℝ)) hmem 8 (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66933/524288 : ℝ))) hcmem 8 (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66933/524288 : ℝ)) (992068502409/1000000000000 : ℝ) (248017125603/250000000000 : ℝ) (50129581803/100000000000 : ℝ) (12532395451/25000000000 : ℝ) (793729089961/1000000000000 : ℝ) (39686454499/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0860_exp_lower
  have heNumeric : (2054901530629/1000000000000 : ℝ)/4 ≤ Real.exp (-4262825160247/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901530629/1000000000000 : ℝ)/4 ≤ Real.exp ((16733/131072 : ℝ)-(39686454499/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16733/131072 : ℝ) (66933/524288 : ℝ) (39686454499/50000000000 : ℝ) (2054901530629/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0861; no trusted numerical premise.
theorem cover8_leaf0861_exp_radius : (49900359981094811/50000000000000000 : ℝ) ≤ Real.exp ((-33467/2097152 : ℝ)/8) ∧ Real.exp ((-33467/2097152 : ℝ)/8) ≤ (998007199621896221/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33467/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0861_exp_lower : (920113447621033837/1000000000000000000 : ℝ) ≤ Real.exp ((-85256503203707/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503203707/128000000000000 : ℝ)/8) ≤ (460056723810516919/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503203707/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0861_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862691331/125000000000 : ℝ) ≤ 4*Real.exp (66933/524288 : ℝ)*Real.exp (-mu (radius 8 (33467/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862691331/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33467/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0861_exp_radius
  have hrNumeric : (984168349991/1000000000000 : ℝ) ≤ Real.exp (-33467/2097152 : ℝ) ∧ Real.exp (-33467/2097152 : ℝ) ≤ (123021043749/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984168349991/1000000000000 : ℝ) ≤ (radius 8 (33467/262144 : ℝ)) ∧ (radius 8 (33467/262144 : ℝ)) ≤ (123021043749/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33467/262144 : ℝ)) (984168349991/1000000000000 : ℝ) (123021043749/125000000000 : ℝ) (88618083473/500000000000 : ℝ) (177236166953/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33467/262144 : ℝ)) (984168349991/1000000000000 : ℝ) (123021043749/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33467/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984168349991/1000000000000 : ℝ) (123021043749/125000000000 : ℝ) (198416834999/200000000000 : ℝ) (248021043749/250000000000 : ℝ) (992052594367/1000000000000 : ℝ) (15500821787/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33467/262144 : ℝ)) 1 (198416834999/200000000000 : ℝ) (248021043749/250000000000 : ℝ) (992052594367/1000000000000 : ℝ) (15500821787/15625000000 : ℝ) (992068384681/1000000000000 : ℝ) (496034192341/500000000000 : ℝ) (198413676911/200000000000 : ℝ) (992068384557/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33467/262144 : ℝ)) 2 (992068384681/1000000000000 : ℝ) (496034192341/500000000000 : ℝ) (198413676911/200000000000 : ℝ) (992068384557/1000000000000 : ℝ) (496034192309/500000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33467/262144 : ℝ)) 3 (496034192309/500000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33467/262144 : ℝ)) 4 (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33467/262144 : ℝ)) 5 (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33467/262144 : ℝ)) 6 (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33467/262144 : ℝ)) 7 (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33467/262144 : ℝ))) (88618083473/500000000000 : ℝ) (177236166953/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33467/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88618083473/500000000000 : ℝ) (177236166953/1000000000000 : ℝ) (588618083473/1000000000000 : ℝ) (588618083477/1000000000000 : ℝ) (420994259991/1000000000000 : ℝ) (420994260001/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33467/262144 : ℝ))) 1 (588618083473/1000000000000 : ℝ) (588618083477/1000000000000 : ℝ) (420994259991/1000000000000 : ℝ) (420994260001/1000000000000 : ℝ) (126201542933/250000000000 : ℝ) (504806171739/1000000000000 : ℝ) (124449998611/250000000000 : ℝ) (497799994453/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33467/262144 : ℝ))) 2 (126201542933/250000000000 : ℝ) (504806171739/1000000000000 : ℝ) (124449998611/250000000000 : ℝ) (497799994453/1000000000000 : ℝ) (31331442693/62500000000 : ℝ) (62662885387/125000000000 : ℝ) (501290843207/1000000000000 : ℝ) (31330677701/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33467/262144 : ℝ))) 3 (31331442693/62500000000 : ℝ) (62662885387/125000000000 : ℝ) (501290843207/1000000000000 : ℝ) (31330677701/62500000000 : ℝ) (501296963147/1000000000000 : ℝ) (125324240789/250000000000 : ℝ) (50129696311/100000000000 : ℝ) (501296963119/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33467/262144 : ℝ))) 4 (501296963147/1000000000000 : ℝ) (125324240789/250000000000 : ℝ) (50129696311/100000000000 : ℝ) (501296963119/1000000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33467/262144 : ℝ))) 5 (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33467/262144 : ℝ))) 6 (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33467/262144 : ℝ))) 7 (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33467/262144 : ℝ)) hmem 8 (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33467/262144 : ℝ))) hcmem 8 (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33467/262144 : ℝ)) (992068384617/1000000000000 : ℝ) (49603419231/50000000000 : ℝ) (62662120391/125000000000 : ℝ) (250648481569/500000000000 : ℝ) (7937309973/10000000000 : ℝ) (793730997319/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0861_exp_lower
  have heNumeric : (256862691331/125000000000 : ℝ)/4 ≤ Real.exp (-85256503203707/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862691331/125000000000 : ℝ)/4 ≤ Real.exp ((66933/524288 : ℝ)-(793730997319/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66933/524288 : ℝ) (33467/262144 : ℝ) (793730997319/1000000000000 : ℝ) (256862691331/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0862; no trusted numerical premise.
theorem cover8_leaf0862_exp_radius : (199601433975792871/200000000000000000 : ℝ) ≤ Real.exp ((-66935/4194304 : ℝ)/8) ∧ Real.exp ((-66935/4194304 : ℝ)/8) ≤ (249501792469741089/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66935/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0862_exp_lower : (920113447624442031/1000000000000000000 : ℝ) ≤ Real.exp ((-42628251599957/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251599957/64000000000000 : ℝ)/8) ≤ (57507090476527627/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251599957/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0862_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901530709/1000000000000 : ℝ) ≤ 4*Real.exp (33467/262144 : ℝ)*Real.exp (-mu (radius 8 (66935/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901530709/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66935/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0862_exp_radius
  have hrNumeric : (984168115347/1000000000000 : ℝ) ≤ Real.exp (-66935/4194304 : ℝ) ∧ Real.exp (-66935/4194304 : ℝ) ≤ (246042028837/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984168115347/1000000000000 : ℝ) ≤ (radius 8 (66935/524288 : ℝ)) ∧ (radius 8 (66935/524288 : ℝ)) ≤ (246042028837/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66935/524288 : ℝ)) (984168115347/1000000000000 : ℝ) (246042028837/250000000000 : ℝ) (2769335467/15625000000 : ℝ) (88618734947/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66935/524288 : ℝ)) (984168115347/1000000000000 : ℝ) (246042028837/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66935/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984168115347/1000000000000 : ℝ) (246042028837/250000000000 : ℝ) (992084057673/1000000000000 : ℝ) (496042028837/500000000000 : ℝ) (198410495221/200000000000 : ℝ) (496026238053/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66935/524288 : ℝ)) 1 (992084057673/1000000000000 : ℝ) (496042028837/500000000000 : ℝ) (198410495221/200000000000 : ℝ) (496026238053/500000000000 : ℝ) (992068266889/1000000000000 : ℝ) (99206826689/100000000000 : ℝ) (992068266763/1000000000000 : ℝ) (198413653353/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66935/524288 : ℝ)) 2 (992068266889/1000000000000 : ℝ) (99206826689/100000000000 : ℝ) (992068266763/1000000000000 : ℝ) (198413653353/200000000000 : ℝ) (496034133413/500000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66935/524288 : ℝ)) 3 (496034133413/500000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66935/524288 : ℝ)) 4 (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66935/524288 : ℝ)) 5 (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66935/524288 : ℝ)) 6 (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66935/524288 : ℝ)) 7 (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66935/524288 : ℝ))) (2769335467/15625000000 : ℝ) (88618734947/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66935/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2769335467/15625000000 : ℝ) (88618734947/500000000000 : ℝ) (18394335467/31250000000 : ℝ) (588618734947/1000000000000 : ℝ) (420995807447/1000000000000 : ℝ) (84199161491/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66935/524288 : ℝ))) 1 (18394335467/31250000000 : ℝ) (588618734947/1000000000000 : ℝ) (420995807447/1000000000000 : ℝ) (84199161491/200000000000 : ℝ) (100961454239/200000000000 : ℝ) (504807271201/1000000000000 : ℝ) (497801184807/1000000000000 : ℝ) (248900592407/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66935/524288 : ℝ))) 2 (100961454239/200000000000 : ℝ) (504807271201/1000000000000 : ℝ) (497801184807/1000000000000 : ℝ) (248900592407/500000000000 : ℝ) (501304228001/1000000000000 : ℝ) (62663028501/125000000000 : ℝ) (100258397693/200000000000 : ℝ) (501291988473/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66935/524288 : ℝ))) 3 (501304228001/1000000000000 : ℝ) (62663028501/125000000000 : ℝ) (100258397693/200000000000 : ℝ) (501291988473/1000000000000 : ℝ) (501298108233/1000000000000 : ℝ) (501298108241/1000000000000 : ℝ) (100259621639/200000000000 : ℝ) (125324527051/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66935/524288 : ℝ))) 4 (501298108233/1000000000000 : ℝ) (501298108241/1000000000000 : ℝ) (100259621639/200000000000 : ℝ) (125324527051/250000000000 : ℝ) (250649054107/500000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66935/524288 : ℝ))) 5 (250649054107/500000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66935/524288 : ℝ))) 6 (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66935/524288 : ℝ))) 7 (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66935/524288 : ℝ)) hmem 8 (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66935/524288 : ℝ))) hcmem 8 (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66935/524288 : ℝ)) (39682730673/40000000000 : ℝ) (248017066707/250000000000 : ℝ) (501298108213/1000000000000 : ℝ) (501298108223/1000000000000 : ℝ) (793732904619/1000000000000 : ℝ) (396866452319/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0862_exp_lower
  have heNumeric : (2054901530709/1000000000000 : ℝ)/4 ≤ Real.exp (-42628251599957/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901530709/1000000000000 : ℝ)/4 ≤ Real.exp ((33467/262144 : ℝ)-(396866452319/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33467/262144 : ℝ) (66935/524288 : ℝ) (396866452319/500000000000 : ℝ) (2054901530709/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0863; no trusted numerical premise.
theorem cover8_leaf0863_exp_radius : (31187723129251043/31250000000000000 : ℝ) ≤ Real.exp ((-8367/524288 : ℝ)/8) ∧ Real.exp ((-8367/524288 : ℝ)/8) ≤ (998007140136033377/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8367/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0863_exp_lower : (460056723815017747/500000000000000000 : ℝ) ≤ Real.exp ((-85256503193689/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503193689/128000000000000 : ℝ)/8) ≤ (184022689526007099/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503193689/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0863_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901530809/1000000000000 : ℝ) ≤ 4*Real.exp (66935/524288 : ℝ)*Real.exp (-mu (radius 8 (8367/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901530809/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8367/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0863_exp_radius
  have hrNumeric : (984167880703/1000000000000 : ℝ) ≤ Real.exp (-8367/524288 : ℝ) ∧ Real.exp (-8367/524288 : ℝ) ≤ (480550723/488281250 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984167880703/1000000000000 : ℝ) ≤ (radius 8 (8367/65536 : ℝ)) ∧ (radius 8 (8367/65536 : ℝ)) ≤ (480550723/488281250 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8367/65536 : ℝ)) (984167880703/1000000000000 : ℝ) (480550723/488281250 : ℝ) (177238772819/1000000000000 : ℝ) (88619386413/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8367/65536 : ℝ)) (984167880703/1000000000000 : ℝ) (480550723/488281250 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8367/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984167880703/1000000000000 : ℝ) (480550723/488281250 : ℝ) (992083940351/1000000000000 : ℝ) (968831973/976562500 : ℝ) (992052357843/1000000000000 : ℝ) (198410471569/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8367/65536 : ℝ)) 1 (992083940351/1000000000000 : ℝ) (968831973/976562500 : ℝ) (992052357843/1000000000000 : ℝ) (198410471569/200000000000 : ℝ) (992068149097/1000000000000 : ℝ) (992068149099/1000000000000 : ℝ) (992068148971/1000000000000 : ℝ) (992068148973/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8367/65536 : ℝ)) 2 (992068149097/1000000000000 : ℝ) (992068149099/1000000000000 : ℝ) (992068148971/1000000000000 : ℝ) (992068148973/1000000000000 : ℝ) (496034074517/500000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8367/65536 : ℝ)) 3 (496034074517/500000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8367/65536 : ℝ)) 4 (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8367/65536 : ℝ)) 5 (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8367/65536 : ℝ)) 6 (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8367/65536 : ℝ)) 7 (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8367/65536 : ℝ))) (177238772819/1000000000000 : ℝ) (88619386413/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8367/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177238772819/1000000000000 : ℝ) (88619386413/500000000000 : ℝ) (588619386409/1000000000000 : ℝ) (588619386413/1000000000000 : ℝ) (420997354883/1000000000000 : ℝ) (105249338723/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8367/65536 : ℝ))) 1 (588619386409/1000000000000 : ℝ) (588619386413/1000000000000 : ℝ) (420997354883/1000000000000 : ℝ) (105249338723/250000000000 : ℝ) (252404185323/500000000000 : ℝ) (504808370653/1000000000000 : ℝ) (124450593789/250000000000 : ℝ) (124450593791/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8367/65536 : ℝ))) 2 (252404185323/500000000000 : ℝ) (504808370653/1000000000000 : ℝ) (124450593789/250000000000 : ℝ) (124450593791/250000000000 : ℝ) (501305372901/1000000000000 : ℝ) (501305372909/1000000000000 : ℝ) (501293133711/1000000000000 : ℝ) (501293133719/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8367/65536 : ℝ))) 3 (501305372901/1000000000000 : ℝ) (501305372909/1000000000000 : ℝ) (501293133711/1000000000000 : ℝ) (501293133719/1000000000000 : ℝ) (250649626653/500000000000 : ℝ) (250649626657/500000000000 : ℝ) (125324813317/250000000000 : ℝ) (501299253277/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8367/65536 : ℝ))) 4 (250649626653/500000000000 : ℝ) (250649626657/500000000000 : ℝ) (125324813317/250000000000 : ℝ) (501299253277/1000000000000 : ℝ) (501299253287/1000000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8367/65536 : ℝ))) 5 (501299253287/1000000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8367/65536 : ℝ))) 6 (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8367/65536 : ℝ))) 7 (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8367/65536 : ℝ)) hmem 8 (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8367/65536 : ℝ))) hcmem 8 (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8367/65536 : ℝ)) (992068149033/1000000000000 : ℝ) (248017037259/250000000000 : ℝ) (250649626643/500000000000 : ℝ) (31331203331/62500000000 : ℝ) (793734811919/1000000000000 : ℝ) (396867405969/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0863_exp_lower
  have heNumeric : (2054901530809/1000000000000 : ℝ)/4 ≤ Real.exp (-85256503193689/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901530809/1000000000000 : ℝ)/4 ≤ Real.exp ((66935/524288 : ℝ)-(396867405969/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66935/524288 : ℝ) (8367/65536 : ℝ) (396867405969/500000000000 : ℝ) (2054901530809/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0864; no trusted numerical premise.
theorem cover8_leaf0864_exp_radius : (249501777598275821/250000000000000000 : ℝ) ≤ Real.exp ((-66937/4194304 : ℝ)/8) ∧ Real.exp ((-66937/4194304 : ℝ)/8) ≤ (199601422078620657/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66937/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0864_exp_lower : (460056723819424677/500000000000000000 : ℝ) ≤ Real.exp ((-2131412579597/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131412579597/3200000000000 : ℝ)/8) ≤ (184022689527769871/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131412579597/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0864_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901530967/1000000000000 : ℝ) ≤ 4*Real.exp (8367/65536 : ℝ)*Real.exp (-mu (radius 8 (66937/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901530967/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66937/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0864_exp_radius
  have hrNumeric : (49208382303/50000000000 : ℝ) ≤ Real.exp (-66937/4194304 : ℝ) ∧ Real.exp (-66937/4194304 : ℝ) ≤ (984167646061/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49208382303/50000000000 : ℝ) ≤ (radius 8 (66937/524288 : ℝ)) ∧ (radius 8 (66937/524288 : ℝ)) ≤ (984167646061/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66937/524288 : ℝ)) (49208382303/50000000000 : ℝ) (984167646061/1000000000000 : ℝ) (35448015147/200000000000 : ℝ) (88620037871/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66937/524288 : ℝ)) (49208382303/50000000000 : ℝ) (984167646061/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66937/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49208382303/50000000000 : ℝ) (984167646061/1000000000000 : ℝ) (99208382303/100000000000 : ℝ) (992083823031/1000000000000 : ℝ) (496026119791/500000000000 : ℝ) (992052239583/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66937/524288 : ℝ)) 1 (99208382303/100000000000 : ℝ) (992083823031/1000000000000 : ℝ) (496026119791/500000000000 : ℝ) (992052239583/1000000000000 : ℝ) (496034015653/500000000000 : ℝ) (992068031307/1000000000000 : ℝ) (49603401559/50000000000 : ℝ) (496034015591/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66937/524288 : ℝ)) 2 (496034015653/500000000000 : ℝ) (992068031307/1000000000000 : ℝ) (49603401559/50000000000 : ℝ) (496034015591/500000000000 : ℝ) (992068031243/1000000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66937/524288 : ℝ)) 3 (992068031243/1000000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66937/524288 : ℝ)) 4 (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66937/524288 : ℝ)) 5 (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66937/524288 : ℝ)) 6 (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66937/524288 : ℝ)) 7 (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66937/524288 : ℝ))) (35448015147/200000000000 : ℝ) (88620037871/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66937/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35448015147/200000000000 : ℝ) (88620037871/500000000000 : ℝ) (588620037867/1000000000000 : ℝ) (588620037871/1000000000000 : ℝ) (52624862787/125000000000 : ℝ) (84199780461/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66937/524288 : ℝ))) 1 (588620037867/1000000000000 : ℝ) (588620037871/1000000000000 : ℝ) (52624862787/125000000000 : ℝ) (84199780461/200000000000 : ℝ) (504809470081/1000000000000 : ℝ) (63101183761/125000000000 : ℝ) (248901782743/500000000000 : ℝ) (248901782747/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66937/524288 : ℝ))) 2 (504809470081/1000000000000 : ℝ) (63101183761/125000000000 : ℝ) (248901782743/500000000000 : ℝ) (248901782747/500000000000 : ℝ) (501306517783/1000000000000 : ℝ) (501306517791/1000000000000 : ℝ) (501294278939/1000000000000 : ℝ) (501294278947/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66937/524288 : ℝ))) 3 (501306517783/1000000000000 : ℝ) (501306517791/1000000000000 : ℝ) (501294278939/1000000000000 : ℝ) (501294278947/1000000000000 : ℝ) (501300398361/1000000000000 : ℝ) (501300398369/1000000000000 : ℝ) (501300398323/1000000000000 : ℝ) (125325099583/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66937/524288 : ℝ))) 4 (501300398361/1000000000000 : ℝ) (501300398369/1000000000000 : ℝ) (501300398323/1000000000000 : ℝ) (125325099583/250000000000 : ℝ) (250650199171/500000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66937/524288 : ℝ))) 5 (250650199171/500000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66937/524288 : ℝ))) 6 (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66937/524288 : ℝ))) 7 (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66937/524288 : ℝ)) hmem 8 (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66937/524288 : ℝ))) hcmem 8 (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66937/524288 : ℝ)) (496034015621/500000000000 : ℝ) (198413606249/200000000000 : ℝ) (501300398341/1000000000000 : ℝ) (501300398351/1000000000000 : ℝ) (793736719191/1000000000000 : ℝ) (79373671921/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0864_exp_lower
  have heNumeric : (2054901530967/1000000000000 : ℝ)/4 ≤ Real.exp (-2131412579597/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901530967/1000000000000 : ℝ)/4 ≤ Real.exp ((8367/65536 : ℝ)-(79373671921/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8367/65536 : ℝ) (66937/524288 : ℝ) (79373671921/100000000000 : ℝ) (2054901530967/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0865; no trusted numerical premise.
theorem cover8_leaf0865_exp_radius : (499003540325087039/500000000000000000 : ℝ) ≤ Real.exp ((-33469/2097152 : ℝ)/8) ∧ Real.exp ((-33469/2097152 : ℝ)/8) ≤ (998007080650174079/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33469/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0865_exp_lower : (460056723824349171/500000000000000000 : ℝ) ≤ Real.exp ((-85256503172919/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503172919/128000000000000 : ℝ)/8) ≤ (920113447648698343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503172919/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0865_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901531143/1000000000000 : ℝ) ≤ 4*Real.exp (66937/524288 : ℝ)*Real.exp (-mu (radius 8 (33469/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901531143/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33469/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0865_exp_radius
  have hrNumeric : (123020926427/125000000000 : ℝ) ≤ Real.exp (-33469/2097152 : ℝ) ∧ Real.exp (-33469/2097152 : ℝ) ≤ (984167411417/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123020926427/125000000000 : ℝ) ≤ (radius 8 (33469/262144 : ℝ)) ∧ (radius 8 (33469/262144 : ℝ)) ≤ (984167411417/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33469/262144 : ℝ)) (123020926427/125000000000 : ℝ) (984167411417/1000000000000 : ℝ) (177241378647/1000000000000 : ℝ) (177241378653/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33469/262144 : ℝ)) (123020926427/125000000000 : ℝ) (984167411417/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33469/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123020926427/125000000000 : ℝ) (984167411417/1000000000000 : ℝ) (248020926427/250000000000 : ℝ) (992083705709/1000000000000 : ℝ) (24801303033/25000000000 : ℝ) (992052121321/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33469/262144 : ℝ)) 1 (248020926427/250000000000 : ℝ) (992083705709/1000000000000 : ℝ) (24801303033/25000000000 : ℝ) (992052121321/1000000000000 : ℝ) (496033956757/500000000000 : ℝ) (198413582703/200000000000 : ℝ) (248016978347/250000000000 : ℝ) (99206791339/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33469/262144 : ℝ)) 2 (496033956757/500000000000 : ℝ) (198413582703/200000000000 : ℝ) (248016978347/250000000000 : ℝ) (99206791339/100000000000 : ℝ) (992067913451/1000000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33469/262144 : ℝ)) 3 (992067913451/1000000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33469/262144 : ℝ)) 4 (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33469/262144 : ℝ)) 5 (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33469/262144 : ℝ)) 6 (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33469/262144 : ℝ)) 7 (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33469/262144 : ℝ))) (177241378647/1000000000000 : ℝ) (177241378653/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33469/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177241378647/1000000000000 : ℝ) (177241378653/1000000000000 : ℝ) (588620689323/1000000000000 : ℝ) (588620689327/1000000000000 : ℝ) (421000449699/1000000000000 : ℝ) (421000449707/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33469/262144 : ℝ))) 1 (588620689323/1000000000000 : ℝ) (588620689327/1000000000000 : ℝ) (421000449699/1000000000000 : ℝ) (421000449707/1000000000000 : ℝ) (504810569511/1000000000000 : ℝ) (504810569517/1000000000000 : ℝ) (49780475581/100000000000 : ℝ) (497804755817/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33469/262144 : ℝ))) 2 (504810569511/1000000000000 : ℝ) (504810569517/1000000000000 : ℝ) (49780475581/100000000000 : ℝ) (497804755817/1000000000000 : ℝ) (25065383133/50000000000 : ℝ) (501307662667/1000000000000 : ℝ) (501295424161/1000000000000 : ℝ) (501295424169/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33469/262144 : ℝ))) 3 (25065383133/50000000000 : ℝ) (501307662667/1000000000000 : ℝ) (501295424161/1000000000000 : ℝ) (501295424169/1000000000000 : ℝ) (50130154341/100000000000 : ℝ) (250650771709/500000000000 : ℝ) (501301543373/1000000000000 : ℝ) (501301543381/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33469/262144 : ℝ))) 4 (50130154341/100000000000 : ℝ) (250650771709/500000000000 : ℝ) (501301543373/1000000000000 : ℝ) (501301543381/1000000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33469/262144 : ℝ))) 5 (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33469/262144 : ℝ))) 6 (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33469/262144 : ℝ))) 7 (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33469/262144 : ℝ)) hmem 8 (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33469/262144 : ℝ))) hcmem 8 (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33469/262144 : ℝ)) (19841358269/20000000000 : ℝ) (992067913453/1000000000000 : ℝ) (501301543391/1000000000000 : ℝ) (2506507717/5000000000 : ℝ) (158747725291/200000000000 : ℝ) (793738626473/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0865_exp_lower
  have heNumeric : (2054901531143/1000000000000 : ℝ)/4 ≤ Real.exp (-85256503172919/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901531143/1000000000000 : ℝ)/4 ≤ Real.exp ((66937/524288 : ℝ)-(793738626473/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66937/524288 : ℝ) (33469/262144 : ℝ) (793738626473/1000000000000 : ℝ) (2054901531143/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0866; no trusted numerical premise.
theorem cover8_leaf0866_exp_radius : (499003525453622879/500000000000000000 : ℝ) ≤ Real.exp ((-66939/4194304 : ℝ)/8) ∧ Real.exp ((-66939/4194304 : ℝ)/8) ≤ (998007050907245759/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66939/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0866_exp_lower : (184022689532123517/200000000000000000 : ℝ) ≤ Real.exp ((-42628251579827/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251579827/64000000000000 : ℝ)/8) ≤ (460056723830308793/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251579827/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0866_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725382839/250000000000 : ℝ) ≤ 4*Real.exp (33469/262144 : ℝ)*Real.exp (-mu (radius 8 (66939/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725382839/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66939/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0866_exp_radius
  have hrNumeric : (246041794193/250000000000 : ℝ) ≤ Real.exp (-66939/4194304 : ℝ) ∧ Real.exp (-66939/4194304 : ℝ) ≤ (984167176773/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246041794193/250000000000 : ℝ) ≤ (radius 8 (66939/524288 : ℝ)) ∧ (radius 8 (66939/524288 : ℝ)) ≤ (984167176773/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66939/524288 : ℝ)) (246041794193/250000000000 : ℝ) (984167176773/1000000000000 : ℝ) (44310670387/250000000000 : ℝ) (35448536311/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66939/524288 : ℝ)) (246041794193/250000000000 : ℝ) (984167176773/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66939/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246041794193/250000000000 : ℝ) (984167176773/1000000000000 : ℝ) (496041794193/500000000000 : ℝ) (992083588387/1000000000000 : ℝ) (496026001529/500000000000 : ℝ) (992052003059/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66939/524288 : ℝ)) 1 (496041794193/500000000000 : ℝ) (992083588387/1000000000000 : ℝ) (496026001529/500000000000 : ℝ) (992052003059/1000000000000 : ℝ) (496033897861/500000000000 : ℝ) (992067795723/1000000000000 : ℝ) (248016948899/250000000000 : ℝ) (496033897799/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66939/524288 : ℝ)) 2 (496033897861/500000000000 : ℝ) (992067795723/1000000000000 : ℝ) (248016948899/250000000000 : ℝ) (496033897799/500000000000 : ℝ) (992067795659/1000000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66939/524288 : ℝ)) 3 (992067795659/1000000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66939/524288 : ℝ)) 4 (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66939/524288 : ℝ)) 5 (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66939/524288 : ℝ)) 6 (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66939/524288 : ℝ)) 7 (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66939/524288 : ℝ))) (44310670387/250000000000 : ℝ) (35448536311/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66939/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44310670387/250000000000 : ℝ) (35448536311/200000000000 : ℝ) (294310670387/500000000000 : ℝ) (294310670389/500000000000 : ℝ) (421001997083/1000000000000 : ℝ) (105250499273/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66939/524288 : ℝ))) 1 (294310670387/500000000000 : ℝ) (294310670389/500000000000 : ℝ) (421001997083/1000000000000 : ℝ) (105250499273/250000000000 : ℝ) (7887682327/15625000000 : ℝ) (100962333787/200000000000 : ℝ) (497805946119/1000000000000 : ℝ) (497805946127/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66939/524288 : ℝ))) 2 (7887682327/15625000000 : ℝ) (100962333787/200000000000 : ℝ) (497805946119/1000000000000 : ℝ) (497805946127/1000000000000 : ℝ) (501308807523/1000000000000 : ℝ) (501308807531/1000000000000 : ℝ) (50129656937/100000000000 : ℝ) (250648284689/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66939/524288 : ℝ))) 3 (501308807523/1000000000000 : ℝ) (501308807531/1000000000000 : ℝ) (50129656937/100000000000 : ℝ) (250648284689/500000000000 : ℝ) (250651344223/500000000000 : ℝ) (100260537691/200000000000 : ℝ) (501302688409/1000000000000 : ℝ) (250651344209/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66939/524288 : ℝ))) 4 (250651344223/500000000000 : ℝ) (100260537691/200000000000 : ℝ) (501302688409/1000000000000 : ℝ) (250651344209/500000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66939/524288 : ℝ))) 5 (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66939/524288 : ℝ))) 6 (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66939/524288 : ℝ))) 7 (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66939/524288 : ℝ)) hmem 8 (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66939/524288 : ℝ))) hcmem 8 (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66939/524288 : ℝ)) (496033897829/500000000000 : ℝ) (992067795661/1000000000000 : ℝ) (501302688427/1000000000000 : ℝ) (501302688437/1000000000000 : ℝ) (396870266849/500000000000 : ℝ) (396870266859/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0866_exp_lower
  have heNumeric : (513725382839/250000000000 : ℝ)/4 ≤ Real.exp (-42628251579827/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725382839/250000000000 : ℝ)/4 ≤ Real.exp ((33469/262144 : ℝ)-(396870266859/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33469/262144 : ℝ) (66939/524288 : ℝ) (396870266859/500000000000 : ℝ) (513725382839/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0867; no trusted numerical premise.
theorem cover8_leaf0867_exp_radius : (39920280846572733/40000000000000000 : ℝ) ≤ Real.exp ((-16735/1048576 : ℝ)/8) ∧ Real.exp ((-16735/1048576 : ℝ)/8) ≤ (499003510582159163/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16735/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0867_exp_lower : (460056723837476063/500000000000000000 : ℝ) ≤ Real.exp ((-85256503143701/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503143701/128000000000000 : ℝ)/8) ≤ (920113447674952127/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503143701/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0867_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725382903/250000000000 : ℝ) ≤ 4*Real.exp (66939/524288 : ℝ)*Real.exp (-mu (radius 8 (16735/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725382903/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16735/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0867_exp_radius
  have hrNumeric : (61510433883/62500000000 : ℝ) ≤ Real.exp (-16735/1048576 : ℝ) ∧ Real.exp (-16735/1048576 : ℝ) ≤ (984166942129/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61510433883/62500000000 : ℝ) ≤ (radius 8 (16735/131072 : ℝ)) ∧ (radius 8 (16735/131072 : ℝ)) ≤ (984166942129/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16735/131072 : ℝ)) (61510433883/62500000000 : ℝ) (984166942129/1000000000000 : ℝ) (4431099611/25000000000 : ℝ) (177243984447/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16735/131072 : ℝ)) (61510433883/62500000000 : ℝ) (984166942129/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16735/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61510433883/62500000000 : ℝ) (984166942129/1000000000000 : ℝ) (124010433883/125000000000 : ℝ) (198416694213/200000000000 : ℝ) (248012971199/250000000000 : ℝ) (992051884797/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16735/131072 : ℝ)) 1 (124010433883/125000000000 : ℝ) (198416694213/200000000000 : ℝ) (248012971199/250000000000 : ℝ) (992051884797/1000000000000 : ℝ) (99206767793/100000000000 : ℝ) (992067677931/1000000000000 : ℝ) (248016919451/250000000000 : ℝ) (496033838903/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16735/131072 : ℝ)) 2 (99206767793/100000000000 : ℝ) (992067677931/1000000000000 : ℝ) (248016919451/250000000000 : ℝ) (496033838903/500000000000 : ℝ) (992067677867/1000000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16735/131072 : ℝ)) 3 (992067677867/1000000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16735/131072 : ℝ)) 4 (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16735/131072 : ℝ)) 5 (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16735/131072 : ℝ)) 6 (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16735/131072 : ℝ)) 7 (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16735/131072 : ℝ))) (4431099611/25000000000 : ℝ) (177243984447/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16735/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4431099611/25000000000 : ℝ) (177243984447/1000000000000 : ℝ) (29431099611/50000000000 : ℝ) (18394437257/31250000000 : ℝ) (8420070889/20000000000 : ℝ) (421003544459/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16735/131072 : ℝ))) 1 (29431099611/50000000000 : ℝ) (18394437257/31250000000 : ℝ) (8420070889/20000000000 : ℝ) (421003544459/1000000000000 : ℝ) (100962553667/200000000000 : ℝ) (252406384171/500000000000 : ℝ) (99561427283/200000000000 : ℝ) (497807136423/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16735/131072 : ℝ))) 2 (100962553667/200000000000 : ℝ) (252406384171/500000000000 : ℝ) (99561427283/200000000000 : ℝ) (497807136423/1000000000000 : ℝ) (4010479619/8000000000 : ℝ) (501309952383/1000000000000 : ℝ) (501297714567/1000000000000 : ℝ) (20051908583/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16735/131072 : ℝ))) 3 (4010479619/8000000000 : ℝ) (501309952383/1000000000000 : ℝ) (501297714567/1000000000000 : ℝ) (20051908583/40000000000 : ℝ) (501303833471/1000000000000 : ℝ) (501303833479/1000000000000 : ℝ) (501303833433/1000000000000 : ℝ) (250651916721/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16735/131072 : ℝ))) 4 (501303833471/1000000000000 : ℝ) (501303833479/1000000000000 : ℝ) (501303833433/1000000000000 : ℝ) (250651916721/500000000000 : ℝ) (125325958363/250000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16735/131072 : ℝ))) 5 (125325958363/250000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16735/131072 : ℝ))) 6 (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16735/131072 : ℝ))) 7 (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16735/131072 : ℝ)) hmem 8 (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16735/131072 : ℝ))) hcmem 8 (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16735/131072 : ℝ)) (496033838933/500000000000 : ℝ) (992067677869/1000000000000 : ℝ) (501303833451/1000000000000 : ℝ) (501303833461/1000000000000 : ℝ) (793742440923/1000000000000 : ℝ) (396871220471/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0867_exp_lower
  have heNumeric : (513725382903/250000000000 : ℝ)/4 ≤ Real.exp (-85256503143701/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725382903/250000000000 : ℝ)/4 ≤ Real.exp ((66939/524288 : ℝ)-(396871220471/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66939/524288 : ℝ) (16735/131072 : ℝ) (396871220471/500000000000 : ℝ) (513725382903/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0868; no trusted numerical premise.
theorem cover8_leaf0868_exp_radius : (499003495710695889/500000000000000000 : ℝ) ≤ Real.exp ((-66941/4194304 : ℝ)/8) ∧ Real.exp ((-66941/4194304 : ℝ)/8) ≤ (998006991421391779/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66941/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0868_exp_lower : (920113447692392049/1000000000000000000 : ℝ) ≤ Real.exp ((-21314125781073/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125781073/32000000000000 : ℝ)/8) ≤ (18402268953847841/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125781073/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0868_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901531923/1000000000000 : ℝ) ≤ 4*Real.exp (16735/131072 : ℝ)*Real.exp (-mu (radius 8 (66941/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901531923/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66941/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0868_exp_radius
  have hrNumeric : (196833341497/200000000000 : ℝ) ≤ Real.exp (-66941/4194304 : ℝ) ∧ Real.exp (-66941/4194304 : ℝ) ≤ (492083353743/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196833341497/200000000000 : ℝ) ≤ (radius 8 (66941/524288 : ℝ)) ∧ (radius 8 (66941/524288 : ℝ)) ≤ (492083353743/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66941/524288 : ℝ)) (196833341497/200000000000 : ℝ) (492083353743/500000000000 : ℝ) (177245287317/1000000000000 : ℝ) (177245287323/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66941/524288 : ℝ)) (196833341497/200000000000 : ℝ) (492083353743/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66941/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196833341497/200000000000 : ℝ) (492083353743/500000000000 : ℝ) (496041676871/500000000000 : ℝ) (992083353743/1000000000000 : ℝ) (496025883267/500000000000 : ℝ) (124006470817/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66941/524288 : ℝ)) 1 (496041676871/500000000000 : ℝ) (992083353743/1000000000000 : ℝ) (496025883267/500000000000 : ℝ) (124006470817/125000000000 : ℝ) (496033780069/500000000000 : ℝ) (49603378007/50000000000 : ℝ) (248016890003/250000000000 : ℝ) (496033780007/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66941/524288 : ℝ)) 2 (496033780069/500000000000 : ℝ) (49603378007/50000000000 : ℝ) (248016890003/250000000000 : ℝ) (496033780007/500000000000 : ℝ) (39682702403/40000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66941/524288 : ℝ)) 3 (39682702403/40000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66941/524288 : ℝ)) 4 (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66941/524288 : ℝ)) 5 (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66941/524288 : ℝ)) 6 (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66941/524288 : ℝ)) 7 (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66941/524288 : ℝ))) (177245287317/1000000000000 : ℝ) (177245287323/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66941/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177245287317/1000000000000 : ℝ) (177245287323/1000000000000 : ℝ) (294311321829/500000000000 : ℝ) (294311321831/500000000000 : ℝ) (210502545897/500000000000 : ℝ) (210502545901/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66941/524288 : ℝ))) 1 (294311321829/500000000000 : ℝ) (294311321831/500000000000 : ℝ) (210502545897/500000000000 : ℝ) (210502545901/500000000000 : ℝ) (252406933863/500000000000 : ℝ) (126203466933/250000000000 : ℝ) (497808326693/1000000000000 : ℝ) (4978083267/10000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66941/524288 : ℝ))) 2 (252406933863/500000000000 : ℝ) (126203466933/250000000000 : ℝ) (497808326693/1000000000000 : ℝ) (4978083267/10000000000 : ℝ) (501311097209/1000000000000 : ℝ) (3916492947/7812500000 : ℝ) (501298859747/1000000000000 : ℝ) (250649429877/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66941/524288 : ℝ))) 3 (501311097209/1000000000000 : ℝ) (3916492947/7812500000 : ℝ) (501298859747/1000000000000 : ℝ) (250649429877/500000000000 : ℝ) (250652489239/500000000000 : ℝ) (100260995697/200000000000 : ℝ) (12532624461/25000000000 : ℝ) (31331561153/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66941/524288 : ℝ))) 4 (250652489239/500000000000 : ℝ) (100260995697/200000000000 : ℝ) (12532624461/25000000000 : ℝ) (31331561153/62500000000 : ℝ) (501304978459/1000000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66941/524288 : ℝ))) 5 (501304978459/1000000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66941/524288 : ℝ))) 6 (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66941/524288 : ℝ))) 7 (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66941/524288 : ℝ)) hmem 8 (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66941/524288 : ℝ))) hcmem 8 (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66941/524288 : ℝ)) (496033780037/500000000000 : ℝ) (992067560077/1000000000000 : ℝ) (250652489229/500000000000 : ℝ) (501304978467/1000000000000 : ℝ) (793744348121/1000000000000 : ℝ) (793744348139/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0868_exp_lower
  have heNumeric : (2054901531923/1000000000000 : ℝ)/4 ≤ Real.exp (-21314125781073/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901531923/1000000000000 : ℝ)/4 ≤ Real.exp ((16735/131072 : ℝ)-(793744348139/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16735/131072 : ℝ) (66941/524288 : ℝ) (793744348139/1000000000000 : ℝ) (2054901531923/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0869; no trusted numerical premise.
theorem cover8_leaf0869_exp_radius : (499003480839233059/500000000000000000 : ℝ) ≤ Real.exp ((-33471/2097152 : ℝ)/8) ∧ Real.exp ((-33471/2097152 : ℝ)/8) ≤ (998006961678466119/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33471/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0869_exp_lower : (920113447710752087/1000000000000000000 : ℝ) ≤ Real.exp ((-85256503103859/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503103859/128000000000000 : ℝ)/8) ≤ (115014180963844011/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503103859/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0869_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901532251/1000000000000 : ℝ) ≤ 4*Real.exp (66941/524288 : ℝ)*Real.exp (-mu (radius 8 (33471/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901532251/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33471/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0869_exp_radius
  have hrNumeric : (984166472841/1000000000000 : ℝ) ≤ Real.exp (-33471/2097152 : ℝ) ∧ Real.exp (-33471/2097152 : ℝ) ≤ (492083236421/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984166472841/1000000000000 : ℝ) ≤ (radius 8 (33471/262144 : ℝ)) ∧ (radius 8 (33471/262144 : ℝ)) ≤ (492083236421/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33471/262144 : ℝ)) (984166472841/1000000000000 : ℝ) (492083236421/500000000000 : ℝ) (177246590189/1000000000000 : ℝ) (35449318039/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33471/262144 : ℝ)) (984166472841/1000000000000 : ℝ) (492083236421/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33471/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984166472841/1000000000000 : ℝ) (492083236421/500000000000 : ℝ) (49604161821/50000000000 : ℝ) (992083236421/1000000000000 : ℝ) (62003228017/62500000000 : ℝ) (496025824137/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33471/262144 : ℝ)) 1 (49604161821/50000000000 : ℝ) (992083236421/1000000000000 : ℝ) (62003228017/62500000000 : ℝ) (496025824137/500000000000 : ℝ) (496033721173/500000000000 : ℝ) (248016860587/250000000000 : ℝ) (49603372111/50000000000 : ℝ) (496033721111/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33471/262144 : ℝ)) 2 (496033721173/500000000000 : ℝ) (248016860587/250000000000 : ℝ) (49603372111/50000000000 : ℝ) (496033721111/500000000000 : ℝ) (992067442283/1000000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33471/262144 : ℝ)) 3 (992067442283/1000000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33471/262144 : ℝ)) 4 (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33471/262144 : ℝ)) 5 (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33471/262144 : ℝ)) 6 (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33471/262144 : ℝ)) 7 (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33471/262144 : ℝ))) (177246590189/1000000000000 : ℝ) (35449318039/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33471/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177246590189/1000000000000 : ℝ) (35449318039/200000000000 : ℝ) (294311647547/500000000000 : ℝ) (294311647549/500000000000 : ℝ) (210503319563/500000000000 : ℝ) (84201327827/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33471/262144 : ℝ))) 1 (294311647547/500000000000 : ℝ) (294311647549/500000000000 : ℝ) (210503319563/500000000000 : ℝ) (84201327827/200000000000 : ℝ) (50481496711/100000000000 : ℝ) (504814967117/1000000000000 : ℝ) (248904758481/500000000000 : ℝ) (49780951697/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33471/262144 : ℝ))) 2 (50481496711/100000000000 : ℝ) (504814967117/1000000000000 : ℝ) (248904758481/500000000000 : ℝ) (49780951697/100000000000 : ℝ) (125328060509/250000000000 : ℝ) (125328060511/250000000000 : ℝ) (501300004919/1000000000000 : ℝ) (501300004927/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33471/262144 : ℝ))) 3 (125328060509/250000000000 : ℝ) (125328060511/250000000000 : ℝ) (501300004919/1000000000000 : ℝ) (501300004927/1000000000000 : ℝ) (501306123477/1000000000000 : ℝ) (250653061743/500000000000 : ℝ) (6266326543/12500000000 : ℝ) (501306123449/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33471/262144 : ℝ))) 4 (501306123477/1000000000000 : ℝ) (250653061743/500000000000 : ℝ) (6266326543/12500000000 : ℝ) (501306123449/1000000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33471/262144 : ℝ))) 5 (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33471/262144 : ℝ))) 6 (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33471/262144 : ℝ))) 7 (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33471/262144 : ℝ)) hmem 8 (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33471/262144 : ℝ))) hcmem 8 (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33471/262144 : ℝ)) (496033721141/500000000000 : ℝ) (198413488457/200000000000 : ℝ) (250653061729/500000000000 : ℝ) (125326530867/250000000000 : ℝ) (198436563827/250000000000 : ℝ) (24804570479/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0869_exp_lower
  have heNumeric : (2054901532251/1000000000000 : ℝ)/4 ≤ Real.exp (-85256503103859/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901532251/1000000000000 : ℝ)/4 ≤ Real.exp ((66941/524288 : ℝ)-(24804570479/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66941/524288 : ℝ) (33471/262144 : ℝ) (24804570479/31250000000 : ℝ) (2054901532251/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0870; no trusted numerical premise.
theorem cover8_leaf0870_exp_radius : (31187716622985667/31250000000000000 : ℝ) ≤ Real.exp ((-66943/4194304 : ℝ)/8) ∧ Real.exp ((-66943/4194304 : ℝ)/8) ≤ (199601386387108269/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66943/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0870_exp_lower : (920113447731412407/1000000000000000000 : ℝ) ≤ Real.exp ((-42628251540433/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251540433/64000000000000 : ℝ)/8) ≤ (115014180966426551/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251540433/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0870_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745076631/50000000000 : ℝ) ≤ 4*Real.exp (33471/262144 : ℝ)*Real.exp (-mu (radius 8 (66943/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (102745076631/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66943/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0870_exp_radius
  have hrNumeric : (984166238197/1000000000000 : ℝ) ≤ Real.exp (-66943/4194304 : ℝ) ∧ Real.exp (-66943/4194304 : ℝ) ≤ (492083119099/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984166238197/1000000000000 : ℝ) ≤ (radius 8 (66943/524288 : ℝ)) ∧ (radius 8 (66943/524288 : ℝ)) ≤ (492083119099/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66943/524288 : ℝ)) (984166238197/1000000000000 : ℝ) (492083119099/500000000000 : ℝ) (177247893051/1000000000000 : ℝ) (88623946529/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66943/524288 : ℝ)) (984166238197/1000000000000 : ℝ) (492083119099/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66943/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984166238197/1000000000000 : ℝ) (492083119099/500000000000 : ℝ) (496041559549/500000000000 : ℝ) (992083119099/1000000000000 : ℝ) (99205153001/100000000000 : ℝ) (248012882503/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66943/524288 : ℝ)) 1 (496041559549/500000000000 : ℝ) (992083119099/1000000000000 : ℝ) (99205153001/100000000000 : ℝ) (248012882503/250000000000 : ℝ) (496033662277/500000000000 : ℝ) (248016831139/250000000000 : ℝ) (248016831107/250000000000 : ℝ) (99206732443/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66943/524288 : ℝ)) 2 (496033662277/500000000000 : ℝ) (248016831139/250000000000 : ℝ) (248016831107/250000000000 : ℝ) (99206732443/100000000000 : ℝ) (992067324491/1000000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66943/524288 : ℝ)) 3 (992067324491/1000000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66943/524288 : ℝ)) 4 (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66943/524288 : ℝ)) 5 (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66943/524288 : ℝ)) 6 (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66943/524288 : ℝ)) 7 (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66943/524288 : ℝ))) (177247893051/1000000000000 : ℝ) (88623946529/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66943/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177247893051/1000000000000 : ℝ) (88623946529/500000000000 : ℝ) (23544957861/40000000000 : ℝ) (588623946529/1000000000000 : ℝ) (421008186441/1000000000000 : ℝ) (421008186451/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66943/524288 : ℝ))) 1 (23544957861/40000000000 : ℝ) (588623946529/1000000000000 : ℝ) (421008186441/1000000000000 : ℝ) (421008186451/1000000000000 : ℝ) (504816066483/1000000000000 : ℝ) (50481606649/100000000000 : ℝ) (497810707219/1000000000000 : ℝ) (497810707227/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66943/524288 : ℝ))) 2 (504816066483/1000000000000 : ℝ) (50481606649/100000000000 : ℝ) (497810707219/1000000000000 : ℝ) (497810707227/1000000000000 : ℝ) (501313386851/1000000000000 : ℝ) (501313386859/1000000000000 : ℝ) (501301150079/1000000000000 : ℝ) (62662643761/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66943/524288 : ℝ))) 3 (501313386851/1000000000000 : ℝ) (501313386859/1000000000000 : ℝ) (501301150079/1000000000000 : ℝ) (62662643761/125000000000 : ℝ) (100261453693/200000000000 : ℝ) (250653634237/500000000000 : ℝ) (501307268427/1000000000000 : ℝ) (501307268437/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66943/524288 : ℝ))) 4 (100261453693/200000000000 : ℝ) (250653634237/500000000000 : ℝ) (501307268427/1000000000000 : ℝ) (501307268437/1000000000000 : ℝ) (250653634223/500000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66943/524288 : ℝ))) 5 (250653634223/500000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66943/524288 : ℝ))) 6 (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66943/524288 : ℝ))) 7 (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66943/524288 : ℝ)) hmem 8 (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66943/524288 : ℝ))) hcmem 8 (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66943/524288 : ℝ)) (99206732449/100000000000 : ℝ) (992067324493/1000000000000 : ℝ) (100261453689/200000000000 : ℝ) (62663408557/125000000000 : ℝ) (198437040619/250000000000 : ℝ) (793748162497/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0870_exp_lower
  have heNumeric : (102745076631/50000000000 : ℝ)/4 ≤ Real.exp (-42628251540433/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745076631/50000000000 : ℝ)/4 ≤ Real.exp ((33471/262144 : ℝ)-(793748162497/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33471/262144 : ℝ) (66943/524288 : ℝ) (793748162497/1000000000000 : ℝ) (102745076631/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0871; no trusted numerical premise.
theorem cover8_leaf0871_exp_radius : (998006902192617457/1000000000000000000 : ℝ) ≤ Real.exp ((-523/32768 : ℝ)/8) ∧ Real.exp ((-523/32768 : ℝ)/8) ≤ (499003451096308729/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-523/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0871_exp_lower : (920113447755408139/1000000000000000000 : ℝ) ≤ Real.exp ((-85256503054161/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256503054161/128000000000000 : ℝ)/8) ≤ (46005672387770407/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256503054161/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0871_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901533049/1000000000000 : ℝ) ≤ 4*Real.exp (66943/524288 : ℝ)*Real.exp (-mu (radius 8 (523/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901533049/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (523/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0871_exp_radius
  have hrNumeric : (492083001777/500000000000 : ℝ) ≤ Real.exp (-523/32768 : ℝ) ∧ Real.exp (-523/32768 : ℝ) ≤ (196833200711/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492083001777/500000000000 : ℝ) ≤ (radius 8 (523/4096 : ℝ)) ∧ (radius 8 (523/4096 : ℝ)) ≤ (196833200711/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (523/4096 : ℝ)) (492083001777/500000000000 : ℝ) (196833200711/200000000000 : ℝ) (88624597949/500000000000 : ℝ) (1384759343/7812500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (523/4096 : ℝ)) (492083001777/500000000000 : ℝ) (196833200711/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (523/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492083001777/500000000000 : ℝ) (196833200711/200000000000 : ℝ) (992083001777/1000000000000 : ℝ) (496041500889/500000000000 : ℝ) (992051411749/1000000000000 : ℝ) (3968205647/4000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (523/4096 : ℝ)) 1 (992083001777/1000000000000 : ℝ) (496041500889/500000000000 : ℝ) (992051411749/1000000000000 : ℝ) (3968205647/4000000000 : ℝ) (992067206763/1000000000000 : ℝ) (248016801691/250000000000 : ℝ) (992067206637/1000000000000 : ℝ) (992067206639/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (523/4096 : ℝ)) 2 (992067206763/1000000000000 : ℝ) (248016801691/250000000000 : ℝ) (992067206637/1000000000000 : ℝ) (992067206639/1000000000000 : ℝ) (9920672067/10000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (523/4096 : ℝ)) 3 (9920672067/10000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (523/4096 : ℝ)) 4 (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (523/4096 : ℝ)) 5 (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (523/4096 : ℝ)) 6 (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (523/4096 : ℝ)) 7 (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (523/4096 : ℝ))) (88624597949/500000000000 : ℝ) (1384759343/7812500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (523/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88624597949/500000000000 : ℝ) (1384759343/7812500000 : ℝ) (588624597949/1000000000000 : ℝ) (9197259343/15625000000 : ℝ) (421009733733/1000000000000 : ℝ) (421009733741/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (523/4096 : ℝ))) 1 (588624597949/1000000000000 : ℝ) (9197259343/15625000000 : ℝ) (421009733733/1000000000000 : ℝ) (421009733741/1000000000000 : ℝ) (504817165841/1000000000000 : ℝ) (504817165847/1000000000000 : ℝ) (248905948729/500000000000 : ℝ) (99562379493/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (523/4096 : ℝ))) 2 (504817165841/1000000000000 : ℝ) (504817165847/1000000000000 : ℝ) (248905948729/500000000000 : ℝ) (99562379493/200000000000 : ℝ) (501314531649/1000000000000 : ℝ) (62664316457/125000000000 : ℝ) (501302295223/1000000000000 : ℝ) (501302295231/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (523/4096 : ℝ))) 3 (501314531649/1000000000000 : ℝ) (62664316457/125000000000 : ℝ) (501302295223/1000000000000 : ℝ) (501302295231/1000000000000 : ℝ) (125327103359/250000000000 : ℝ) (125327103361/250000000000 : ℝ) (250654206699/500000000000 : ℝ) (501308413407/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (523/4096 : ℝ))) 4 (125327103359/250000000000 : ℝ) (125327103361/250000000000 : ℝ) (250654206699/500000000000 : ℝ) (501308413407/1000000000000 : ℝ) (501308413417/1000000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (523/4096 : ℝ))) 5 (501308413417/1000000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (523/4096 : ℝ))) 6 (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (523/4096 : ℝ))) 7 (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (523/4096 : ℝ)) hmem 8 (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (523/4096 : ℝ))) hcmem 8 (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (523/4096 : ℝ)) (992067206699/1000000000000 : ℝ) (496033603351/500000000000 : ℝ) (62663551677/125000000000 : ℝ) (250654206713/500000000000 : ℝ) (793750069617/1000000000000 : ℝ) (793750069637/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0871_exp_lower
  have heNumeric : (2054901533049/1000000000000 : ℝ)/4 ≤ Real.exp (-85256503054161/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901533049/1000000000000 : ℝ)/4 ≤ Real.exp ((66943/524288 : ℝ)-(793750069637/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66943/524288 : ℝ) (523/4096 : ℝ) (793750069637/1000000000000 : ℝ) (2054901533049/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0872; no trusted numerical premise.
theorem cover8_leaf0872_exp_radius : (124750859056211807/125000000000000000 : ℝ) ≤ Real.exp ((-66945/4194304 : ℝ)/8) ∧ Real.exp ((-66945/4194304 : ℝ)/8) ≤ (998006872449694457/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66945/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0872_exp_lower : (920113447781474127/1000000000000000000 : ℝ) ≤ Real.exp ((-166516607471/250000000000 : ℝ)/8) ∧ Real.exp ((-166516607471/250000000000 : ℝ)/8) ≤ (57507090486342133/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166516607471/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0872_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980306703/200000000000 : ℝ) ≤ 4*Real.exp (523/4096 : ℝ)*Real.exp (-mu (radius 8 (66945/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980306703/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66945/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0872_exp_radius
  have hrNumeric : (984165768911/1000000000000 : ℝ) ≤ Real.exp (-66945/4194304 : ℝ) ∧ Real.exp (-66945/4194304 : ℝ) ≤ (61510360557/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984165768911/1000000000000 : ℝ) ≤ (radius 8 (66945/524288 : ℝ)) ∧ (radius 8 (66945/524288 : ℝ)) ≤ (61510360557/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66945/524288 : ℝ)) (984165768911/1000000000000 : ℝ) (61510360557/62500000000 : ℝ) (35450099747/200000000000 : ℝ) (177250498741/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66945/524288 : ℝ)) (984165768911/1000000000000 : ℝ) (61510360557/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66945/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984165768911/1000000000000 : ℝ) (61510360557/62500000000 : ℝ) (198416576891/200000000000 : ℝ) (124010360557/125000000000 : ℝ) (992051293487/1000000000000 : ℝ) (992051293489/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66945/524288 : ℝ)) 1 (198416576891/200000000000 : ℝ) (124010360557/125000000000 : ℝ) (992051293487/1000000000000 : ℝ) (992051293489/1000000000000 : ℝ) (992067088971/1000000000000 : ℝ) (992067088973/1000000000000 : ℝ) (198413417769/200000000000 : ℝ) (992067088847/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66945/524288 : ℝ)) 2 (992067088971/1000000000000 : ℝ) (992067088973/1000000000000 : ℝ) (198413417769/200000000000 : ℝ) (992067088847/1000000000000 : ℝ) (248016772227/250000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66945/524288 : ℝ)) 3 (248016772227/250000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66945/524288 : ℝ)) 4 (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66945/524288 : ℝ)) 5 (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66945/524288 : ℝ)) 6 (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66945/524288 : ℝ)) 7 (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66945/524288 : ℝ))) (35450099747/200000000000 : ℝ) (177250498741/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66945/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35450099747/200000000000 : ℝ) (177250498741/1000000000000 : ℝ) (588625249367/1000000000000 : ℝ) (588625249371/1000000000000 : ℝ) (210505640503/500000000000 : ℝ) (210505640507/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66945/524288 : ℝ))) 1 (588625249367/1000000000000 : ℝ) (588625249371/1000000000000 : ℝ) (210505640503/500000000000 : ℝ) (210505640507/500000000000 : ℝ) (252409132593/500000000000 : ℝ) (504818265193/1000000000000 : ℝ) (248906543841/500000000000 : ℝ) (49781308769/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66945/524288 : ℝ))) 2 (252409132593/500000000000 : ℝ) (504818265193/1000000000000 : ℝ) (248906543841/500000000000 : ℝ) (49781308769/100000000000 : ℝ) (250657838217/500000000000 : ℝ) (250657838221/500000000000 : ℝ) (501303440353/1000000000000 : ℝ) (250651720181/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66945/524288 : ℝ))) 3 (250657838217/500000000000 : ℝ) (250657838221/500000000000 : ℝ) (501303440353/1000000000000 : ℝ) (250651720181/500000000000 : ℝ) (501309558393/1000000000000 : ℝ) (250654779201/500000000000 : ℝ) (125327389589/250000000000 : ℝ) (100261911673/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66945/524288 : ℝ))) 4 (501309558393/1000000000000 : ℝ) (250654779201/500000000000 : ℝ) (125327389589/250000000000 : ℝ) (100261911673/200000000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66945/524288 : ℝ))) 5 (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66945/524288 : ℝ))) 6 (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66945/524288 : ℝ))) 7 (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66945/524288 : ℝ)) hmem 8 (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66945/524288 : ℝ))) hcmem 8 (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66945/524288 : ℝ)) (992067088907/1000000000000 : ℝ) (99206708891/100000000000 : ℝ) (250654779187/500000000000 : ℝ) (31331847399/62500000000 : ℝ) (39687598837/50000000000 : ℝ) (793751976759/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0872_exp_lower
  have heNumeric : (410980306703/200000000000 : ℝ)/4 ≤ Real.exp (-166516607471/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980306703/200000000000 : ℝ)/4 ≤ Real.exp ((523/4096 : ℝ)-(793751976759/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (523/4096 : ℝ) (66945/524288 : ℝ) (793751976759/1000000000000 : ℝ) (410980306703/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0873; no trusted numerical premise.
theorem cover8_leaf0873_exp_radius : (998006842706772341/1000000000000000000 : ℝ) ≤ Real.exp ((-33473/2097152 : ℝ)/8) ∧ Real.exp ((-33473/2097152 : ℝ)/8) ≤ (499003421353386171/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33473/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0873_exp_lower : (92011344780880527/100000000000000000 : ℝ) ≤ Real.exp ((-17051300598947/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051300598947/25600000000000 : ℝ)/8) ≤ (920113447808805271/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051300598947/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0873_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901534003/1000000000000 : ℝ) ≤ 4*Real.exp (66945/524288 : ℝ)*Real.exp (-mu (radius 8 (33473/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901534003/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33473/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0873_exp_radius
  have hrNumeric : (984165534267/1000000000000 : ℝ) ≤ Real.exp (-33473/2097152 : ℝ) ∧ Real.exp (-33473/2097152 : ℝ) ≤ (246041383567/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984165534267/1000000000000 : ℝ) ≤ (radius 8 (33473/262144 : ℝ)) ∧ (radius 8 (33473/262144 : ℝ)) ≤ (246041383567/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33473/262144 : ℝ)) (984165534267/1000000000000 : ℝ) (246041383567/250000000000 : ℝ) (177251801567/1000000000000 : ℝ) (88625900787/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33473/262144 : ℝ)) (984165534267/1000000000000 : ℝ) (246041383567/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33473/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984165534267/1000000000000 : ℝ) (246041383567/250000000000 : ℝ) (992082767133/1000000000000 : ℝ) (496041383567/500000000000 : ℝ) (39682047009/40000000000 : ℝ) (992051175227/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33473/262144 : ℝ)) 1 (992082767133/1000000000000 : ℝ) (496041383567/500000000000 : ℝ) (39682047009/40000000000 : ℝ) (992051175227/1000000000000 : ℝ) (992066971179/1000000000000 : ℝ) (992066971181/1000000000000 : ℝ) (992066971053/1000000000000 : ℝ) (198413394211/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33473/262144 : ℝ)) 2 (992066971179/1000000000000 : ℝ) (992066971181/1000000000000 : ℝ) (992066971053/1000000000000 : ℝ) (198413394211/200000000000 : ℝ) (248016742779/250000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33473/262144 : ℝ)) 3 (248016742779/250000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33473/262144 : ℝ)) 4 (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33473/262144 : ℝ)) 5 (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33473/262144 : ℝ)) 6 (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33473/262144 : ℝ)) 7 (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33473/262144 : ℝ))) (177251801567/1000000000000 : ℝ) (88625900787/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33473/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177251801567/1000000000000 : ℝ) (88625900787/500000000000 : ℝ) (588625900783/1000000000000 : ℝ) (588625900787/1000000000000 : ℝ) (105253207067/250000000000 : ℝ) (210506414139/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33473/262144 : ℝ))) 1 (588625900783/1000000000000 : ℝ) (588625900787/1000000000000 : ℝ) (105253207067/250000000000 : ℝ) (210506414139/500000000000 : ℝ) (20192774581/40000000000 : ℝ) (504819364533/1000000000000 : ℝ) (497814277899/1000000000000 : ℝ) (497814277907/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33473/262144 : ℝ))) 2 (20192774581/40000000000 : ℝ) (504819364533/1000000000000 : ℝ) (497814277899/1000000000000 : ℝ) (497814277907/1000000000000 : ℝ) (125329205303/250000000000 : ℝ) (25065841061/50000000000 : ℝ) (501304585477/1000000000000 : ℝ) (250652292743/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33473/262144 : ℝ))) 3 (125329205303/250000000000 : ℝ) (25065841061/50000000000 : ℝ) (501304585477/1000000000000 : ℝ) (250652292743/500000000000 : ℝ) (31331918959/62500000000 : ℝ) (501310703353/1000000000000 : ℝ) (501310703307/1000000000000 : ℝ) (125327675829/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33473/262144 : ℝ))) 4 (31331918959/62500000000 : ℝ) (501310703353/1000000000000 : ℝ) (501310703307/1000000000000 : ℝ) (125327675829/250000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33473/262144 : ℝ))) 5 (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33473/262144 : ℝ))) 6 (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33473/262144 : ℝ))) 7 (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33473/262144 : ℝ)) hmem 8 (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33473/262144 : ℝ))) hcmem 8 (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33473/262144 : ℝ)) (198413394223/200000000000 : ℝ) (496033485559/500000000000 : ℝ) (20052428133/40000000000 : ℝ) (100262140667/200000000000 : ℝ) (793753883851/1000000000000 : ℝ) (79375388387/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0873_exp_lower
  have heNumeric : (2054901534003/1000000000000 : ℝ)/4 ≤ Real.exp (-17051300598947/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901534003/1000000000000 : ℝ)/4 ≤ Real.exp ((66945/524288 : ℝ)-(79375388387/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66945/524288 : ℝ) (33473/262144 : ℝ) (79375388387/100000000000 : ℝ) (2054901534003/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0874; no trusted numerical premise.
theorem cover8_leaf0874_exp_radius : (998006812963851113/1000000000000000000 : ℝ) ≤ Real.exp ((-66947/4194304 : ℝ)/8) ∧ Real.exp ((-66947/4194304 : ℝ)/8) ≤ (499003406481925557/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66947/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0874_exp_lower : (460056723919563391/500000000000000000 : ℝ) ≤ Real.exp ((-8525650296099/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525650296099/12800000000000 : ℝ)/8) ≤ (920113447839126783/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525650296099/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0874_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980306909/200000000000 : ℝ) ≤ 4*Real.exp (33473/262144 : ℝ)*Real.exp (-mu (radius 8 (66947/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980306909/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66947/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0874_exp_radius
  have hrNumeric : (123020662453/125000000000 : ℝ) ≤ Real.exp (-66947/4194304 : ℝ) ∧ Real.exp (-66947/4194304 : ℝ) ≤ (7873322397/8000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123020662453/125000000000 : ℝ) ≤ (radius 8 (66947/524288 : ℝ)) ∧ (radius 8 (66947/524288 : ℝ)) ≤ (7873322397/8000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66947/524288 : ℝ)) (123020662453/125000000000 : ℝ) (7873322397/8000000000 : ℝ) (692394939/3906250000 : ℝ) (177253104391/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66947/524288 : ℝ)) (123020662453/125000000000 : ℝ) (7873322397/8000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66947/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123020662453/125000000000 : ℝ) (7873322397/8000000000 : ℝ) (248020662453/250000000000 : ℝ) (992082649813/1000000000000 : ℝ) (248012764241/250000000000 : ℝ) (198410211393/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66947/524288 : ℝ)) 1 (248020662453/250000000000 : ℝ) (992082649813/1000000000000 : ℝ) (248012764241/250000000000 : ℝ) (198410211393/200000000000 : ℝ) (248016713347/250000000000 : ℝ) (992066853389/1000000000000 : ℝ) (496033426631/500000000000 : ℝ) (62004178329/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66947/524288 : ℝ)) 2 (248016713347/250000000000 : ℝ) (992066853389/1000000000000 : ℝ) (496033426631/500000000000 : ℝ) (62004178329/62500000000 : ℝ) (39682674133/40000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66947/524288 : ℝ)) 3 (39682674133/40000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66947/524288 : ℝ)) 4 (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66947/524288 : ℝ)) 5 (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66947/524288 : ℝ)) 6 (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66947/524288 : ℝ)) 7 (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66947/524288 : ℝ))) (692394939/3906250000 : ℝ) (177253104391/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66947/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (692394939/3906250000 : ℝ) (177253104391/1000000000000 : ℝ) (4598644939/7812500000 : ℝ) (147156638049/250000000000 : ℝ) (421014375507/1000000000000 : ℝ) (105253593879/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66947/524288 : ℝ))) 1 (4598644939/7812500000 : ℝ) (147156638049/250000000000 : ℝ) (421014375507/1000000000000 : ℝ) (105253593879/250000000000 : ℝ) (504820463849/1000000000000 : ℝ) (31551278991/62500000000 : ℝ) (248907734049/500000000000 : ℝ) (248907734053/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66947/524288 : ℝ))) 2 (504820463849/1000000000000 : ℝ) (31551278991/62500000000 : ℝ) (248907734049/500000000000 : ℝ) (248907734053/500000000000 : ℝ) (501317965973/1000000000000 : ℝ) (501317965981/1000000000000 : ℝ) (62663216323/125000000000 : ℝ) (15665804081/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66947/524288 : ℝ))) 3 (501317965973/1000000000000 : ℝ) (501317965981/1000000000000 : ℝ) (62663216323/125000000000 : ℝ) (15665804081/31250000000 : ℝ) (250655924139/500000000000 : ℝ) (501311848287/1000000000000 : ℝ) (501311848241/1000000000000 : ℝ) (2005247393/4000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66947/524288 : ℝ))) 4 (250655924139/500000000000 : ℝ) (501311848287/1000000000000 : ℝ) (501311848241/1000000000000 : ℝ) (2005247393/4000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66947/524288 : ℝ))) 5 (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66947/524288 : ℝ))) 6 (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66947/524288 : ℝ))) 7 (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66947/524288 : ℝ)) hmem 8 (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66947/524288 : ℝ))) hcmem 8 (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66947/524288 : ℝ)) (248016713331/250000000000 : ℝ) (992066853327/1000000000000 : ℝ) (501311848259/1000000000000 : ℝ) (501311848269/1000000000000 : ℝ) (99219473867/125000000000 : ℝ) (158751158191/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0874_exp_lower
  have heNumeric : (410980306909/200000000000 : ℝ)/4 ≤ Real.exp (-8525650296099/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980306909/200000000000 : ℝ)/4 ≤ Real.exp ((33473/262144 : ℝ)-(158751158191/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33473/262144 : ℝ) (66947/524288 : ℝ) (158751158191/200000000000 : ℝ) (410980306909/200000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0850_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0850_certificate
#check SmaleRate.Proofs.cover8_leaf0851_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0851_certificate
#check SmaleRate.Proofs.cover8_leaf0852_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0852_certificate
#check SmaleRate.Proofs.cover8_leaf0853_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0853_certificate
#check SmaleRate.Proofs.cover8_leaf0854_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0854_certificate
#check SmaleRate.Proofs.cover8_leaf0855_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0855_certificate
#check SmaleRate.Proofs.cover8_leaf0856_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0856_certificate
#check SmaleRate.Proofs.cover8_leaf0857_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0857_certificate
#check SmaleRate.Proofs.cover8_leaf0858_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0858_certificate
#check SmaleRate.Proofs.cover8_leaf0859_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0859_certificate
#check SmaleRate.Proofs.cover8_leaf0860_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0860_certificate
#check SmaleRate.Proofs.cover8_leaf0861_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0861_certificate
#check SmaleRate.Proofs.cover8_leaf0862_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0862_certificate
#check SmaleRate.Proofs.cover8_leaf0863_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0863_certificate
#check SmaleRate.Proofs.cover8_leaf0864_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0864_certificate
#check SmaleRate.Proofs.cover8_leaf0865_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0865_certificate
#check SmaleRate.Proofs.cover8_leaf0866_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0866_certificate
#check SmaleRate.Proofs.cover8_leaf0867_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0867_certificate
#check SmaleRate.Proofs.cover8_leaf0868_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0868_certificate
#check SmaleRate.Proofs.cover8_leaf0869_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0869_certificate
#check SmaleRate.Proofs.cover8_leaf0870_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0870_certificate
#check SmaleRate.Proofs.cover8_leaf0871_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0871_certificate
#check SmaleRate.Proofs.cover8_leaf0872_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0872_certificate
#check SmaleRate.Proofs.cover8_leaf0873_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0873_certificate
#check SmaleRate.Proofs.cover8_leaf0874_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0874_certificate
