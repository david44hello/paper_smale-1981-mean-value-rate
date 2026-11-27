/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0100; no trusted numerical premise.
theorem cover7_leaf0100_exp_radius : (39906333680821101/40000000000000000 : ℝ) ≤ Real.exp ((-2151/114688 : ℝ)/8) ∧ Real.exp ((-2151/114688 : ℝ)/8) ≤ (498829171010263763/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2151/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0100_exp_lower : (459045379803800531/500000000000000000 : ℝ) ≤ Real.exp ((-1367344425179/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367344425179/2000000000000 : ℝ)/8) ≤ (918090759607601063/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367344425179/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0100_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201903999517/100000000000 : ℝ) ≤ 4*Real.exp (1075/8192 : ℝ)*Real.exp (-mu (radius 7 (2151/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (201903999517/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2151/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0100_exp_radius
  have hrNumeric : (490709776677/500000000000 : ℝ) ≤ Real.exp (-2151/114688 : ℝ) ∧ Real.exp (-2151/114688 : ℝ) ≤ (196283910671/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490709776677/500000000000 : ℝ) ≤ (radius 7 (2151/16384 : ℝ)) ∧ (radius 7 (2151/16384 : ℝ)) ≤ (196283910671/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2151/16384 : ℝ)) (490709776677/500000000000 : ℝ) (196283910671/200000000000 : ℝ) (191874074049/1000000000000 : ℝ) (38374814811/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2151/16384 : ℝ)) (490709776677/500000000000 : ℝ) (196283910671/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2151/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490709776677/500000000000 : ℝ) (196283910671/200000000000 : ℝ) (990709776677/1000000000000 : ℝ) (495354888339/500000000000 : ℝ) (990666216923/1000000000000 : ℝ) (39626648677/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2151/16384 : ℝ)) 1 (990709776677/1000000000000 : ℝ) (495354888339/500000000000 : ℝ) (990666216923/1000000000000 : ℝ) (39626648677/40000000000 : ℝ) (309589999/312500000 : ℝ) (495343998401/500000000000 : ℝ) (12383599957/12500000000 : ℝ) (990687996563/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2151/16384 : ℝ)) 2 (309589999/312500000 : ℝ) (495343998401/500000000000 : ℝ) (12383599957/12500000000 : ℝ) (990687996563/1000000000000 : ℝ) (24767199917/25000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2151/16384 : ℝ)) 3 (24767199917/25000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2151/16384 : ℝ)) 4 (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2151/16384 : ℝ)) 5 (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2151/16384 : ℝ)) 6 (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2151/16384 : ℝ)) 7 (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2151/16384 : ℝ))) (191874074049/1000000000000 : ℝ) (38374814811/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2151/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191874074049/1000000000000 : ℝ) (38374814811/200000000000 : ℝ) (18623032407/31250000000 : ℝ) (148984259257/250000000000 : ℝ) (2737714561/6250000000 : ℝ) (54754291221/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2151/16384 : ℝ))) 1 (18623032407/31250000000 : ℝ) (148984259257/250000000000 : ℝ) (2737714561/6250000000 : ℝ) (54754291221/125000000000 : ℝ) (8077901303/15625000000 : ℝ) (258492841699/500000000000 : ℝ) (510921599261/1000000000000 : ℝ) (127730399817/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2151/16384 : ℝ))) 2 (8077901303/15625000000 : ℝ) (258492841699/500000000000 : ℝ) (510921599261/1000000000000 : ℝ) (127730399817/250000000000 : ℝ) (256976820663/500000000000 : ℝ) (513953641333/1000000000000 : ℝ) (513944697563/1000000000000 : ℝ) (513944697571/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2151/16384 : ℝ))) 3 (256976820663/500000000000 : ℝ) (513953641333/1000000000000 : ℝ) (513944697563/1000000000000 : ℝ) (513944697571/1000000000000 : ℝ) (128487292361/250000000000 : ℝ) (128487292363/250000000000 : ℝ) (20557966777/40000000000 : ℝ) (513949169433/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2151/16384 : ℝ))) 4 (128487292361/250000000000 : ℝ) (128487292363/250000000000 : ℝ) (20557966777/40000000000 : ℝ) (513949169433/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2151/16384 : ℝ))) 5 (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2151/16384 : ℝ))) 6 (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2151/16384 : ℝ))) 7 (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2151/16384 : ℝ)) hmem 8 (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2151/16384 : ℝ))) hcmem 8 (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2151/16384 : ℝ)) (990687996679/1000000000000 : ℝ) (990687996683/1000000000000 : ℝ) (256974584717/500000000000 : ℝ) (513949169443/1000000000000 : ℝ) (203724449627/250000000000 : ℝ) (814897798527/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0100_exp_lower
  have heNumeric : (201903999517/100000000000 : ℝ)/4 ≤ Real.exp (-1367344425179/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201903999517/100000000000 : ℝ)/4 ≤ Real.exp ((1075/8192 : ℝ)-(814897798527/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1075/8192 : ℝ) (2151/16384 : ℝ) (814897798527/1000000000000 : ℝ) (201903999517/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0101; no trusted numerical premise.
theorem cover7_leaf0101_exp_radius : (24941431366495507/25000000000000000 : ℝ) ≤ Real.exp ((-269/14336 : ℝ)/8) ∧ Real.exp ((-269/14336 : ℝ)/8) ≤ (997657254659820281/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-269/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0101_exp_lower : (918090585847264283/1000000000000000000 : ℝ) ≤ Real.exp ((-546938981353/800000000000 : ℝ)/8) ∧ Real.exp ((-546938981353/800000000000 : ℝ)/8) ≤ (229522646461816071/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546938981353/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0101_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (100951846907/50000000000 : ℝ) ≤ 4*Real.exp (2151/16384 : ℝ)*Real.exp (-mu (radius 7 (269/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (100951846907/50000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (269/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0101_exp_radius
  have hrNumeric : (245352749023/250000000000 : ℝ) ≤ Real.exp (-269/14336 : ℝ) ∧ Real.exp (-269/14336 : ℝ) ≤ (981410996093/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245352749023/250000000000 : ℝ) ≤ (radius 7 (269/2048 : ℝ)) ∧ (radius 7 (269/2048 : ℝ)) ≤ (981410996093/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (269/2048 : ℝ)) (245352749023/250000000000 : ℝ) (981410996093/1000000000000 : ℝ) (95958919267/500000000000 : ℝ) (9595891927/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (269/2048 : ℝ)) (245352749023/250000000000 : ℝ) (981410996093/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (269/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245352749023/250000000000 : ℝ) (981410996093/1000000000000 : ℝ) (495352749023/500000000000 : ℝ) (990705498047/1000000000000 : ℝ) (990661897971/1000000000000 : ℝ) (247665474493/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (269/2048 : ℝ)) 1 (495352749023/500000000000 : ℝ) (990705498047/1000000000000 : ℝ) (990661897971/1000000000000 : ℝ) (247665474493/250000000000 : ℝ) (123835462251/125000000000 : ℝ) (99068369801/100000000000 : ℝ) (123835462221/125000000000 : ℝ) (99068369777/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (269/2048 : ℝ)) 2 (123835462251/125000000000 : ℝ) (99068369801/100000000000 : ℝ) (123835462221/125000000000 : ℝ) (99068369777/100000000000 : ℝ) (30958865559/31250000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (269/2048 : ℝ)) 3 (30958865559/31250000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (269/2048 : ℝ)) 4 (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (269/2048 : ℝ)) 5 (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (269/2048 : ℝ)) 6 (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (269/2048 : ℝ)) 7 (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (269/2048 : ℝ))) (95958919267/500000000000 : ℝ) (9595891927/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (269/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95958919267/500000000000 : ℝ) (9595891927/50000000000 : ℝ) (595958919267/1000000000000 : ℝ) (59595891927/100000000000 : ℝ) (219042141227/500000000000 : ℝ) (219042141231/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (269/2048 : ℝ))) 1 (595958919267/1000000000000 : ℝ) (59595891927/100000000000 : ℝ) (219042141227/500000000000 : ℝ) (219042141231/500000000000 : ℝ) (25851080043/50000000000 : ℝ) (258510800433/500000000000 : ℝ) (20438404459/40000000000 : ℝ) (255480055741/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (269/2048 : ℝ))) 2 (25851080043/50000000000 : ℝ) (258510800433/500000000000 : ℝ) (20438404459/40000000000 : ℝ) (255480055741/500000000000 : ℝ) (513990856167/1000000000000 : ℝ) (256995428087/500000000000 : ℝ) (513981920703/1000000000000 : ℝ) (513981920711/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (269/2048 : ℝ))) 3 (513990856167/1000000000000 : ℝ) (256995428087/500000000000 : ℝ) (513981920703/1000000000000 : ℝ) (513981920711/1000000000000 : ℝ) (102797277687/200000000000 : ℝ) (513986388443/1000000000000 : ℝ) (102797277683/200000000000 : ℝ) (64248298553/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (269/2048 : ℝ))) 4 (102797277687/200000000000 : ℝ) (513986388443/1000000000000 : ℝ) (102797277683/200000000000 : ℝ) (64248298553/125000000000 : ℝ) (20559455537/40000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (269/2048 : ℝ))) 5 (20559455537/40000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (269/2048 : ℝ))) 6 (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (269/2048 : ℝ))) 7 (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (269/2048 : ℝ)) hmem 8 (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (269/2048 : ℝ))) hcmem 8 (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (269/2048 : ℝ)) (990683697887/1000000000000 : ℝ) (99068369789/100000000000 : ℝ) (64248298553/125000000000 : ℝ) (256993194217/500000000000 : ℝ) (407480173883/500000000000 : ℝ) (162992069557/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0101_exp_lower
  have heNumeric : (100951846907/50000000000 : ℝ)/4 ≤ Real.exp (-546938981353/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (100951846907/50000000000 : ℝ)/4 ≤ Real.exp ((2151/16384 : ℝ)-(162992069557/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2151/16384 : ℝ) (269/2048 : ℝ) (162992069557/200000000000 : ℝ) (100951846907/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0102; no trusted numerical premise.
theorem cover7_leaf0102_exp_radius : (997656167300298163/1000000000000000000 : ℝ) ≤ Real.exp ((-2153/114688 : ℝ)/8) ∧ Real.exp ((-2153/114688 : ℝ)/8) ≤ (249414041825074541/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2153/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0102_exp_lower : (918090414321018649/1000000000000000000 : ℝ) ≤ Real.exp ((-341837610663/500000000000 : ℝ)/8) ∧ Real.exp ((-341837610663/500000000000 : ℝ)/8) ≤ (18361808286420373/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341837610663/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0102_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (100951696021/50000000000 : ℝ) ≤ 4*Real.exp (269/2048 : ℝ)*Real.exp (-mu (radius 7 (2153/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (100951696021/50000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2153/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0102_exp_radius
  have hrNumeric : (196280487781/200000000000 : ℝ) ≤ Real.exp (-2153/114688 : ℝ) ∧ Real.exp (-2153/114688 : ℝ) ≤ (490701219453/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196280487781/200000000000 : ℝ) ≤ (radius 7 (2153/16384 : ℝ)) ∧ (radius 7 (2153/16384 : ℝ)) ≤ (490701219453/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2153/16384 : ℝ)) (196280487781/200000000000 : ℝ) (490701219453/500000000000 : ℝ) (47990398069/250000000000 : ℝ) (95980796141/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2153/16384 : ℝ)) (196280487781/200000000000 : ℝ) (490701219453/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2153/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196280487781/200000000000 : ℝ) (490701219453/500000000000 : ℝ) (247675304863/250000000000 : ℝ) (990701219453/1000000000000 : ℝ) (990657579037/1000000000000 : ℝ) (990657579039/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2153/16384 : ℝ)) 1 (247675304863/250000000000 : ℝ) (990701219453/1000000000000 : ℝ) (990657579037/1000000000000 : ℝ) (990657579039/1000000000000 : ℝ) (247669849811/250000000000 : ℝ) (495339699623/500000000000 : ℝ) (247669849751/250000000000 : ℝ) (495339699503/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2153/16384 : ℝ)) 2 (247669849811/250000000000 : ℝ) (495339699623/500000000000 : ℝ) (247669849751/250000000000 : ℝ) (495339699503/500000000000 : ℝ) (247669849781/250000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2153/16384 : ℝ)) 3 (247669849781/250000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2153/16384 : ℝ)) 4 (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2153/16384 : ℝ)) 5 (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2153/16384 : ℝ)) 6 (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2153/16384 : ℝ)) 7 (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2153/16384 : ℝ))) (47990398069/250000000000 : ℝ) (95980796141/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2153/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (47990398069/250000000000 : ℝ) (95980796141/500000000000 : ℝ) (297990398069/500000000000 : ℝ) (595980796141/1000000000000 : ℝ) (438134217193/1000000000000 : ℝ) (438134217201/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2153/16384 : ℝ))) 1 (297990398069/500000000000 : ℝ) (595980796141/1000000000000 : ℝ) (438134217193/1000000000000 : ℝ) (438134217201/1000000000000 : ℝ) (103411501333/200000000000 : ℝ) (517057506671/1000000000000 : ℝ) (63874826269/125000000000 : ℝ) (510998610159/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2153/16384 : ℝ))) 2 (103411501333/200000000000 : ℝ) (517057506671/1000000000000 : ℝ) (63874826269/125000000000 : ℝ) (510998610159/1000000000000 : ℝ) (64253507301/125000000000 : ℝ) (102805611683/200000000000 : ℝ) (514019131233/1000000000000 : ℝ) (514019131241/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2153/16384 : ℝ))) 3 (64253507301/125000000000 : ℝ) (102805611683/200000000000 : ℝ) (514019131233/1000000000000 : ℝ) (514019131241/1000000000000 : ℝ) (25701179741/50000000000 : ℝ) (128505898707/250000000000 : ℝ) (514023594801/1000000000000 : ℝ) (514023594809/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2153/16384 : ℝ))) 4 (25701179741/50000000000 : ℝ) (128505898707/250000000000 : ℝ) (514023594801/1000000000000 : ℝ) (514023594809/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2153/16384 : ℝ))) 5 (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2153/16384 : ℝ))) 6 (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2153/16384 : ℝ))) 7 (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2153/16384 : ℝ)) hmem 8 (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2153/16384 : ℝ))) hcmem 8 (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2153/16384 : ℝ)) (990679399123/1000000000000 : ℝ) (495339699563/500000000000 : ℝ) (51402359481/100000000000 : ℝ) (514023594819/1000000000000 : ℝ) (407511438779/500000000000 : ℝ) (101877859697/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0102_exp_lower
  have heNumeric : (100951696021/50000000000 : ℝ)/4 ≤ Real.exp (-341837610663/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (100951696021/50000000000 : ℝ)/4 ≤ Real.exp ((269/2048 : ℝ)-(101877859697/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (269/2048 : ℝ) (2153/16384 : ℝ) (101877859697/125000000000 : ℝ) (100951696021/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0103; no trusted numerical premise.
theorem cover7_leaf0103_exp_radius : (498827539970980587/500000000000000000 : ℝ) ≤ Real.exp ((-1077/57344 : ℝ)/8) ∧ Real.exp ((-1077/57344 : ℝ)/8) ≤ (39906203197678447/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1077/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0103_exp_lower : (459045122513054319/500000000000000000 : ℝ) ≤ Real.exp ((-2734706786071/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734706786071/4000000000000 : ℝ)/8) ≤ (918090245026108639/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734706786071/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0103_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (50475773549/25000000000 : ℝ) ≤ 4*Real.exp (2153/16384 : ℝ)*Real.exp (-mu (radius 7 (1077/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (50475773549/25000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1077/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0103_exp_radius
  have hrNumeric : (15334279403/15625000000 : ℝ) ≤ Real.exp (-1077/57344 : ℝ) ∧ Real.exp (-1077/57344 : ℝ) ≤ (981393881793/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15334279403/15625000000 : ℝ) ≤ (radius 7 (1077/8192 : ℝ)) ∧ (radius 7 (1077/8192 : ℝ)) ≤ (981393881793/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1077/8192 : ℝ)) (15334279403/15625000000 : ℝ) (981393881793/1000000000000 : ℝ) (24000666911/125000000000 : ℝ) (96002667647/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1077/8192 : ℝ)) (15334279403/15625000000 : ℝ) (981393881793/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1077/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15334279403/15625000000 : ℝ) (981393881793/1000000000000 : ℝ) (30959279403/31250000000 : ℝ) (990696940897/1000000000000 : ℝ) (495326630061/500000000000 : ℝ) (247663315031/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1077/8192 : ℝ)) 1 (30959279403/31250000000 : ℝ) (990696940897/1000000000000 : ℝ) (495326630061/500000000000 : ℝ) (247663315031/250000000000 : ℝ) (990675100509/1000000000000 : ℝ) (990675100511/1000000000000 : ℝ) (247668775067/250000000000 : ℝ) (99067510027/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1077/8192 : ℝ)) 2 (990675100509/1000000000000 : ℝ) (990675100511/1000000000000 : ℝ) (247668775067/250000000000 : ℝ) (99067510027/100000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1077/8192 : ℝ)) 3 (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1077/8192 : ℝ)) 4 (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1077/8192 : ℝ)) 5 (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1077/8192 : ℝ)) 6 (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1077/8192 : ℝ)) 7 (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1077/8192 : ℝ))) (24000666911/125000000000 : ℝ) (96002667647/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1077/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (24000666911/125000000000 : ℝ) (96002667647/500000000000 : ℝ) (149000666911/250000000000 : ℝ) (596002667647/1000000000000 : ℝ) (219092066999/500000000000 : ℝ) (219092067003/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1077/8192 : ℝ))) 1 (149000666911/250000000000 : ℝ) (596002667647/1000000000000 : ℝ) (219092066999/500000000000 : ℝ) (219092067003/500000000000 : ℝ) (517093400821/1000000000000 : ℝ) (517093400827/1000000000000 : ℝ) (511037095309/1000000000000 : ℝ) (127759273829/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1077/8192 : ℝ))) 2 (517093400821/1000000000000 : ℝ) (517093400827/1000000000000 : ℝ) (511037095309/1000000000000 : ℝ) (127759273829/250000000000 : ℝ) (102813049613/200000000000 : ℝ) (64258156009/125000000000 : ℝ) (514056329169/1000000000000 : ℝ) (64257041147/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1077/8192 : ℝ))) 3 (102813049613/200000000000 : ℝ) (64258156009/125000000000 : ℝ) (514056329169/1000000000000 : ℝ) (64257041147/125000000000 : ℝ) (514060788617/1000000000000 : ℝ) (32128799289/62500000000 : ℝ) (514060788597/1000000000000 : ℝ) (102812157721/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1077/8192 : ℝ))) 4 (514060788617/1000000000000 : ℝ) (32128799289/62500000000 : ℝ) (514060788597/1000000000000 : ℝ) (102812157721/200000000000 : ℝ) (514060788607/1000000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1077/8192 : ℝ))) 5 (514060788607/1000000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1077/8192 : ℝ))) 6 (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1077/8192 : ℝ))) 7 (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1077/8192 : ℝ)) hmem 8 (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1077/8192 : ℝ))) hcmem 8 (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1077/8192 : ℝ)) (247668775097/250000000000 : ℝ) (990675100391/1000000000000 : ℝ) (257030394303/500000000000 : ℝ) (102812157723/200000000000 : ℝ) (407542693953/500000000000 : ℝ) (203771346981/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0103_exp_lower
  have heNumeric : (50475773549/25000000000 : ℝ)/4 ≤ Real.exp (-2734706786071/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (50475773549/25000000000 : ℝ)/4 ≤ Real.exp ((2153/16384 : ℝ)-(203771346981/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2153/16384 : ℝ) (1077/8192 : ℝ) (203771346981/250000000000 : ℝ) (50475773549/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0104; no trusted numerical premise.
theorem cover7_leaf0104_exp_radius : (997653992584809311/1000000000000000000 : ℝ) ≤ Real.exp ((-2155/114688 : ℝ)/8) ∧ Real.exp ((-2155/114688 : ℝ)/8) ≤ (31176687268275291/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2155/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0104_exp_lower : (229522519490375041/250000000000000000 : ℝ) ≤ Real.exp ((-1367356304551/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367356304551/2000000000000 : ℝ)/8) ≤ (183618015592300033/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367356304551/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0104_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009514001371/500000000000 : ℝ) ≤ 4*Real.exp (1077/8192 : ℝ)*Real.exp (-mu (radius 7 (2155/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009514001371/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2155/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0104_exp_radius
  have hrNumeric : (490692662377/500000000000 : ℝ) ≤ Real.exp (-2155/114688 : ℝ) ∧ Real.exp (-2155/114688 : ℝ) ≤ (196277064951/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490692662377/500000000000 : ℝ) ≤ (radius 7 (2155/16384 : ℝ)) ∧ (radius 7 (2155/16384 : ℝ)) ≤ (196277064951/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2155/16384 : ℝ)) (490692662377/500000000000 : ℝ) (196277064951/200000000000 : ℝ) (48012266893/250000000000 : ℝ) (96024533789/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2155/16384 : ℝ)) (490692662377/500000000000 : ℝ) (196277064951/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2155/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490692662377/500000000000 : ℝ) (196277064951/200000000000 : ℝ) (990692662377/1000000000000 : ℝ) (495346331189/500000000000 : ℝ) (495324470613/500000000000 : ℝ) (247662235307/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2155/16384 : ℝ)) 1 (990692662377/1000000000000 : ℝ) (495346331189/500000000000 : ℝ) (495324470613/500000000000 : ℝ) (247662235307/250000000000 : ℝ) (990670801801/1000000000000 : ℝ) (990670801803/1000000000000 : ℝ) (24766770039/25000000000 : ℝ) (495335400781/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2155/16384 : ℝ)) 2 (990670801801/1000000000000 : ℝ) (990670801803/1000000000000 : ℝ) (24766770039/25000000000 : ℝ) (495335400781/500000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2155/16384 : ℝ)) 3 (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2155/16384 : ℝ)) 4 (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2155/16384 : ℝ)) 5 (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2155/16384 : ℝ)) 6 (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2155/16384 : ℝ)) 7 (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2155/16384 : ℝ))) (48012266893/250000000000 : ℝ) (96024533789/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2155/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48012266893/250000000000 : ℝ) (96024533789/500000000000 : ℝ) (298012266893/500000000000 : ℝ) (596024533789/1000000000000 : ℝ) (438234032877/1000000000000 : ℝ) (87646806577/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2155/16384 : ℝ))) 1 (298012266893/500000000000 : ℝ) (596024533789/1000000000000 : ℝ) (438234032877/1000000000000 : ℝ) (87646806577/200000000000 : ℝ) (517129283331/1000000000000 : ℝ) (517129283337/1000000000000 : ℝ) (511075566951/1000000000000 : ℝ) (255537783479/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2155/16384 : ℝ))) 2 (517129283331/1000000000000 : ℝ) (517129283337/1000000000000 : ℝ) (511075566951/1000000000000 : ℝ) (255537783479/500000000000 : ℝ) (514102425141/1000000000000 : ℝ) (128525606287/250000000000 : ℝ) (514093514513/1000000000000 : ℝ) (514093514521/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2155/16384 : ℝ))) 3 (514102425141/1000000000000 : ℝ) (128525606287/250000000000 : ℝ) (514093514513/1000000000000 : ℝ) (514093514521/1000000000000 : ℝ) (514097969827/1000000000000 : ℝ) (102819593967/200000000000 : ℝ) (514097969807/1000000000000 : ℝ) (64262246227/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2155/16384 : ℝ))) 4 (514097969827/1000000000000 : ℝ) (102819593967/200000000000 : ℝ) (514097969807/1000000000000 : ℝ) (64262246227/125000000000 : ℝ) (514097969817/1000000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2155/16384 : ℝ))) 5 (514097969817/1000000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2155/16384 : ℝ))) 6 (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2155/16384 : ℝ))) 7 (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2155/16384 : ℝ)) hmem 8 (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2155/16384 : ℝ))) hcmem 8 (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2155/16384 : ℝ)) (12383385021/12500000000 : ℝ) (990670801683/1000000000000 : ℝ) (64262246227/125000000000 : ℝ) (257048984913/500000000000 : ℝ) (407573939409/500000000000 : ℝ) (407573939419/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0104_exp_lower
  have heNumeric : (1009514001371/500000000000 : ℝ)/4 ≤ Real.exp (-1367356304551/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009514001371/500000000000 : ℝ)/4 ≤ Real.exp ((1077/8192 : ℝ)-(407573939419/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1077/8192 : ℝ) (2155/16384 : ℝ) (407573939419/500000000000 : ℝ) (1009514001371/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0105; no trusted numerical premise.
theorem cover7_leaf0105_exp_radius : (249413226307210643/250000000000000000 : ℝ) ≤ Real.exp ((-77/4096 : ℝ)/8) ∧ Real.exp ((-77/4096 : ℝ)/8) ≤ (997652905228842573/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-77/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0105_exp_lower : (459044956562333631/500000000000000000 : ℝ) ≤ Real.exp ((-546943670897/800000000000 : ℝ)/8) ∧ Real.exp ((-546943670897/800000000000 : ℝ)/8) ≤ (918089913124667263/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546943670897/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0105_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009512551361/500000000000 : ℝ) ≤ 4*Real.exp (2155/16384 : ℝ)*Real.exp (-mu (radius 7 (539/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (1009512551361/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (539/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0105_exp_radius
  have hrNumeric : (98137676779/100000000000 : ℝ) ≤ Real.exp (-77/4096 : ℝ) ∧ Real.exp (-77/4096 : ℝ) ≤ (981376767791/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98137676779/100000000000 : ℝ) ≤ (radius 7 (539/4096 : ℝ)) ∧ (radius 7 (539/4096 : ℝ)) ≤ (981376767791/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (539/4096 : ℝ)) (98137676779/100000000000 : ℝ) (981376767791/1000000000000 : ℝ) (192092789141/1000000000000 : ℝ) (192092789147/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (539/4096 : ℝ)) (98137676779/100000000000 : ℝ) (981376767791/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (539/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98137676779/100000000000 : ℝ) (981376767791/1000000000000 : ℝ) (198137676779/200000000000 : ℝ) (123836047987/125000000000 : ℝ) (990644622349/1000000000000 : ℝ) (990644622351/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (539/4096 : ℝ)) 1 (198137676779/200000000000 : ℝ) (123836047987/125000000000 : ℝ) (990644622349/1000000000000 : ℝ) (990644622351/1000000000000 : ℝ) (495333251561/500000000000 : ℝ) (247666625781/250000000000 : ℝ) (6191665643/6250000000 : ℝ) (495333251441/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (539/4096 : ℝ)) 2 (495333251561/500000000000 : ℝ) (247666625781/250000000000 : ℝ) (6191665643/6250000000 : ℝ) (495333251441/500000000000 : ℝ) (990666503001/1000000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (539/4096 : ℝ)) 3 (990666503001/1000000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (539/4096 : ℝ)) 4 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (539/4096 : ℝ)) 5 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (539/4096 : ℝ)) 6 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (539/4096 : ℝ)) 7 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (539/4096 : ℝ))) (192092789141/1000000000000 : ℝ) (192092789147/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (539/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192092789141/1000000000000 : ℝ) (192092789147/1000000000000 : ℝ) (59604639457/100000000000 : ℝ) (298023197287/500000000000 : ℝ) (438283913851/1000000000000 : ℝ) (438283913859/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (539/4096 : ℝ))) 1 (59604639457/100000000000 : ℝ) (298023197287/500000000000 : ℝ) (438283913851/1000000000000 : ℝ) (438283913859/1000000000000 : ℝ) (51716515421/100000000000 : ℝ) (517165154217/1000000000000 : ℝ) (102222805019/200000000000 : ℝ) (255557012551/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (539/4096 : ℝ))) 2 (51716515421/100000000000 : ℝ) (517165154217/1000000000000 : ℝ) (102222805019/200000000000 : ℝ) (255557012551/500000000000 : ℝ) (128534897413/250000000000 : ℝ) (25706979483/50000000000 : ℝ) (128532671821/250000000000 : ℝ) (128532671823/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (539/4096 : ℝ))) 3 (128534897413/250000000000 : ℝ) (25706979483/50000000000 : ℝ) (128532671821/250000000000 : ℝ) (128532671823/250000000000 : ℝ) (128533784617/250000000000 : ℝ) (128533784619/250000000000 : ℝ) (32133446153/62500000000 : ℝ) (514135138457/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (539/4096 : ℝ))) 4 (128533784617/250000000000 : ℝ) (128533784619/250000000000 : ℝ) (32133446153/62500000000 : ℝ) (514135138457/1000000000000 : ℝ) (257067569229/500000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (539/4096 : ℝ))) 5 (257067569229/500000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (539/4096 : ℝ))) 6 (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (539/4096 : ℝ))) 7 (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (539/4096 : ℝ)) hmem 8 (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (539/4096 : ℝ))) hcmem 8 (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (539/4096 : ℝ)) (990666503/1000000000 : ℝ) (990666503003/1000000000000 : ℝ) (514135138457/1000000000000 : ℝ) (514135138467/1000000000000 : ℝ) (815210350321/1000000000000 : ℝ) (40760517517/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0105_exp_lower
  have heNumeric : (1009512551361/500000000000 : ℝ)/4 ≤ Real.exp (-546943670897/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009512551361/500000000000 : ℝ)/4 ≤ Real.exp ((2155/16384 : ℝ)-(40760517517/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2155/16384 : ℝ) (539/4096 : ℝ) (40760517517/50000000000 : ℝ) (1009512551361/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0106; no trusted numerical premise.
theorem cover7_leaf0106_exp_radius : (249412954468515239/250000000000000000 : ℝ) ≤ Real.exp ((-2157/114688 : ℝ)/8) ∧ Real.exp ((-2157/114688 : ℝ)/8) ≤ (997651817874060957/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2157/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0106_exp_lower : (229522437628701351/250000000000000000 : ℝ) ≤ Real.exp ((-341840502781/500000000000 : ℝ)/8) ∧ Real.exp ((-341840502781/500000000000 : ℝ)/8) ≤ (183617950102961081/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341840502781/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0106_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403804448377/200000000000 : ℝ) ≤ 4*Real.exp (539/4096 : ℝ)*Real.exp (-mu (radius 7 (2157/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403804448377/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2157/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0106_exp_radius
  have hrNumeric : (981368210901/1000000000000 : ℝ) ≤ Real.exp (-2157/114688 : ℝ) ∧ Real.exp (-2157/114688 : ℝ) ≤ (490684105451/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981368210901/1000000000000 : ℝ) ≤ (radius 7 (2157/16384 : ℝ)) ∧ (radius 7 (2157/16384 : ℝ)) ≤ (490684105451/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2157/16384 : ℝ)) (981368210901/1000000000000 : ℝ) (490684105451/500000000000 : ℝ) (48034124999/250000000000 : ℝ) (96068250001/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2157/16384 : ℝ)) (981368210901/1000000000000 : ℝ) (490684105451/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2157/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981368210901/1000000000000 : ℝ) (490684105451/500000000000 : ℝ) (19813682109/20000000000 : ℝ) (990684105451/1000000000000 : ℝ) (990640303491/1000000000000 : ℝ) (247660075873/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2157/16384 : ℝ)) 1 (19813682109/20000000000 : ℝ) (990684105451/1000000000000 : ℝ) (990640303491/1000000000000 : ℝ) (247660075873/250000000000 : ℝ) (99066220447/100000000000 : ℝ) (123832775559/125000000000 : ℝ) (247665551057/250000000000 : ℝ) (99066220423/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2157/16384 : ℝ)) 2 (99066220447/100000000000 : ℝ) (123832775559/125000000000 : ℝ) (247665551057/250000000000 : ℝ) (99066220423/100000000000 : ℝ) (990662204349/1000000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2157/16384 : ℝ)) 3 (990662204349/1000000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2157/16384 : ℝ)) 4 (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2157/16384 : ℝ)) 5 (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2157/16384 : ℝ)) 6 (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2157/16384 : ℝ)) 7 (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2157/16384 : ℝ))) (48034124999/250000000000 : ℝ) (96068250001/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2157/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48034124999/250000000000 : ℝ) (96068250001/500000000000 : ℝ) (298034124999/500000000000 : ℝ) (596068250001/1000000000000 : ℝ) (13697930529/31250000000 : ℝ) (87666755387/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2157/16384 : ℝ))) 1 (298034124999/500000000000 : ℝ) (596068250001/1000000000000 : ℝ) (13697930529/31250000000 : ℝ) (87666755387/200000000000 : ℝ) (517201013463/1000000000000 : ℝ) (129300253367/250000000000 : ℝ) (511152469747/1000000000000 : ℝ) (511152469753/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2157/16384 : ℝ))) 2 (517201013463/1000000000000 : ℝ) (129300253367/250000000000 : ℝ) (511152469747/1000000000000 : ℝ) (511152469753/1000000000000 : ℝ) (102835348321/200000000000 : ℝ) (514176741611/1000000000000 : ℝ) (128541961871/250000000000 : ℝ) (514167847491/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2157/16384 : ℝ))) 3 (102835348321/200000000000 : ℝ) (514176741611/1000000000000 : ℝ) (128541961871/250000000000 : ℝ) (514167847491/1000000000000 : ℝ) (32135768409/62500000000 : ℝ) (514172294551/1000000000000 : ℝ) (20566891781/40000000000 : ℝ) (128543073633/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2157/16384 : ℝ))) 4 (32135768409/62500000000 : ℝ) (514172294551/1000000000000 : ℝ) (20566891781/40000000000 : ℝ) (128543073633/250000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2157/16384 : ℝ))) 5 (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2157/16384 : ℝ))) 6 (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2157/16384 : ℝ))) 7 (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2157/16384 : ℝ)) hmem 8 (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2157/16384 : ℝ))) hcmem 8 (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2157/16384 : ℝ)) (247665551087/250000000000 : ℝ) (990662204351/1000000000000 : ℝ) (257086147267/500000000000 : ℝ) (257086147271/500000000000 : ℝ) (40763640121/50000000000 : ℝ) (815272802437/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0106_exp_lower
  have heNumeric : (403804448377/200000000000 : ℝ)/4 ≤ Real.exp (-341840502781/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403804448377/200000000000 : ℝ)/4 ≤ Real.exp ((539/4096 : ℝ)-(815272802437/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (539/4096 : ℝ) (2157/16384 : ℝ) (815272802437/1000000000000 : ℝ) (403804448377/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0107; no trusted numerical premise.
theorem cover7_leaf0107_exp_radius : (997650730520464463/1000000000000000000 : ℝ) ≤ Real.exp ((-1079/57344 : ℝ)/8) ∧ Real.exp ((-1079/57344 : ℝ)/8) ≤ (62353170657529029/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1079/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0107_exp_lower : (183617918025785923/200000000000000000 : ℝ) ≤ Real.exp ((-546945922499/800000000000 : ℝ)/8) ∧ Real.exp ((-546945922499/800000000000 : ℝ)/8) ≤ (57380599383058101/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546945922499/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0107_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009509710089/500000000000 : ℝ) ≤ 4*Real.exp (2157/16384 : ℝ)*Real.exp (-mu (radius 7 (1079/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009509710089/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1079/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0107_exp_radius
  have hrNumeric : (490679827043/500000000000 : ℝ) ≤ Real.exp (-1079/57344 : ℝ) ∧ Real.exp (-1079/57344 : ℝ) ≤ (981359654087/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490679827043/500000000000 : ℝ) ≤ (radius 7 (1079/8192 : ℝ)) ∧ (radius 7 (1079/8192 : ℝ)) ≤ (981359654087/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1079/8192 : ℝ)) (490679827043/500000000000 : ℝ) (981359654087/1000000000000 : ℝ) (192180200151/1000000000000 : ℝ) (192180200157/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1079/8192 : ℝ)) (490679827043/500000000000 : ℝ) (981359654087/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1079/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490679827043/500000000000 : ℝ) (981359654087/1000000000000 : ℝ) (990679827043/1000000000000 : ℝ) (247669956761/250000000000 : ℝ) (990635984651/1000000000000 : ℝ) (247658996163/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1079/8192 : ℝ)) 1 (990679827043/1000000000000 : ℝ) (247669956761/250000000000 : ℝ) (990635984651/1000000000000 : ℝ) (247658996163/250000000000 : ℝ) (990657905847/1000000000000 : ℝ) (123832238231/125000000000 : ℝ) (247664476401/250000000000 : ℝ) (495328952803/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1079/8192 : ℝ)) 2 (990657905847/1000000000000 : ℝ) (123832238231/125000000000 : ℝ) (247664476401/250000000000 : ℝ) (495328952803/500000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1079/8192 : ℝ)) 3 (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1079/8192 : ℝ)) 4 (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1079/8192 : ℝ)) 5 (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1079/8192 : ℝ)) 6 (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1079/8192 : ℝ)) 7 (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1079/8192 : ℝ))) (192180200151/1000000000000 : ℝ) (192180200157/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1079/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192180200151/1000000000000 : ℝ) (192180200157/1000000000000 : ℝ) (23843604003/40000000000 : ℝ) (596090100079/1000000000000 : ℝ) (438383622129/1000000000000 : ℝ) (54797952767/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1079/8192 : ℝ))) 1 (23843604003/40000000000 : ℝ) (596090100079/1000000000000 : ℝ) (438383622129/1000000000000 : ℝ) (54797952767/125000000000 : ℝ) (258618430551/500000000000 : ℝ) (129309215277/250000000000 : ℝ) (255595450461/500000000000 : ℝ) (511190900929/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1079/8192 : ℝ))) 2 (258618430551/500000000000 : ℝ) (129309215277/250000000000 : ℝ) (255595450461/500000000000 : ℝ) (511190900929/1000000000000 : ℝ) (128553470253/250000000000 : ℝ) (514213881019/1000000000000 : ℝ) (51420499513/100000000000 : ℝ) (514204995137/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1079/8192 : ℝ))) 3 (128553470253/250000000000 : ℝ) (514213881019/1000000000000 : ℝ) (51420499513/100000000000 : ℝ) (514204995137/1000000000000 : ℝ) (514209438071/1000000000000 : ℝ) (257104719039/500000000000 : ℝ) (514209438051/1000000000000 : ℝ) (514209438059/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1079/8192 : ℝ))) 4 (514209438071/1000000000000 : ℝ) (257104719039/500000000000 : ℝ) (514209438051/1000000000000 : ℝ) (514209438059/1000000000000 : ℝ) (514209438061/1000000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1079/8192 : ℝ))) 5 (514209438061/1000000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1079/8192 : ℝ))) 6 (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1079/8192 : ℝ))) 7 (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1079/8192 : ℝ)) hmem 8 (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1079/8192 : ℝ))) hcmem 8 (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1079/8192 : ℝ)) (39626316229/40000000000 : ℝ) (990657905727/1000000000000 : ℝ) (25710471903/50000000000 : ℝ) (514209438069/1000000000000 : ℝ) (407667617569/500000000000 : ℝ) (163067047031/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0107_exp_lower
  have heNumeric : (1009509710089/500000000000 : ℝ)/4 ≤ Real.exp (-546945922499/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009509710089/500000000000 : ℝ)/4 ≤ Real.exp ((2157/16384 : ℝ)-(163067047031/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2157/16384 : ℝ) (1079/8192 : ℝ) (163067047031/200000000000 : ℝ) (1009509710089/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0108; no trusted numerical premise.
theorem cover7_leaf0108_exp_radius : (99764964316805309/100000000000000000 : ℝ) ≤ Real.exp ((-2159/114688 : ℝ)/8) ∧ Real.exp ((-2159/114688 : ℝ)/8) ≤ (997649643168053091/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2159/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0108_exp_lower : (14345147374483187/15625000000000000 : ℝ) ≤ Real.exp ((-273473512523/400000000000 : ℝ)/8) ∧ Real.exp ((-273473512523/400000000000 : ℝ)/8) ≤ (918089431966923969/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273473512523/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0108_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019016637601/1000000000000 : ℝ) ≤ 4*Real.exp (1079/8192 : ℝ)*Real.exp (-mu (radius 7 (2159/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019016637601/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2159/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0108_exp_radius
  have hrNumeric : (981351097347/1000000000000 : ℝ) ≤ Real.exp (-2159/114688 : ℝ) ∧ Real.exp (-2159/114688 : ℝ) ≤ (245337774337/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981351097347/1000000000000 : ℝ) ≤ (radius 7 (2159/16384 : ℝ)) ∧ (radius 7 (2159/16384 : ℝ)) ≤ (245337774337/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2159/16384 : ℝ)) (981351097347/1000000000000 : ℝ) (245337774337/250000000000 : ℝ) (96111944801/500000000000 : ℝ) (24027986201/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2159/16384 : ℝ)) (981351097347/1000000000000 : ℝ) (245337774337/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2159/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981351097347/1000000000000 : ℝ) (245337774337/250000000000 : ℝ) (990675548673/1000000000000 : ℝ) (495337774337/500000000000 : ℝ) (99063166583/100000000000 : ℝ) (123828958229/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2159/16384 : ℝ)) 1 (990675548673/1000000000000 : ℝ) (495337774337/500000000000 : ℝ) (99063166583/100000000000 : ℝ) (123828958229/125000000000 : ℝ) (990653607251/1000000000000 : ℝ) (990653607253/1000000000000 : ℝ) (30957925219/31250000000 : ℝ) (990653607011/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2159/16384 : ℝ)) 2 (990653607251/1000000000000 : ℝ) (990653607253/1000000000000 : ℝ) (30957925219/31250000000 : ℝ) (990653607011/1000000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2159/16384 : ℝ)) 3 (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2159/16384 : ℝ)) 4 (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2159/16384 : ℝ)) 5 (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2159/16384 : ℝ)) 6 (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2159/16384 : ℝ)) 7 (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2159/16384 : ℝ))) (96111944801/500000000000 : ℝ) (24027986201/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2159/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96111944801/500000000000 : ℝ) (24027986201/125000000000 : ℝ) (596111944801/1000000000000 : ℝ) (149027986201/250000000000 : ℝ) (27402090591/62500000000 : ℝ) (438433449463/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2159/16384 : ℝ))) 1 (596111944801/1000000000000 : ℝ) (149027986201/250000000000 : ℝ) (27402090591/62500000000 : ℝ) (438433449463/1000000000000 : ℝ) (64659087141/125000000000 : ℝ) (258636348567/500000000000 : ℝ) (15975916207/31250000000 : ℝ) (51122931863/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2159/16384 : ℝ))) 2 (64659087141/125000000000 : ℝ) (258636348567/500000000000 : ℝ) (15975916207/31250000000 : ℝ) (51122931863/100000000000 : ℝ) (128562751969/250000000000 : ℝ) (257125503941/500000000000 : ℝ) (257121065111/500000000000 : ℝ) (514242130229/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2159/16384 : ℝ))) 3 (128562751969/250000000000 : ℝ) (257125503941/500000000000 : ℝ) (257121065111/500000000000 : ℝ) (514242130229/1000000000000 : ℝ) (514246569049/1000000000000 : ℝ) (16070205283/31250000000 : ℝ) (514246569029/1000000000000 : ℝ) (514246569037/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2159/16384 : ℝ))) 4 (514246569049/1000000000000 : ℝ) (16070205283/31250000000 : ℝ) (514246569029/1000000000000 : ℝ) (514246569037/1000000000000 : ℝ) (514246569039/1000000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2159/16384 : ℝ))) 5 (514246569039/1000000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2159/16384 : ℝ))) 6 (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2159/16384 : ℝ))) 7 (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2159/16384 : ℝ)) hmem 8 (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2159/16384 : ℝ))) hcmem 8 (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2159/16384 : ℝ)) (990653607129/1000000000000 : ℝ) (247663401783/250000000000 : ℝ) (257123284519/500000000000 : ℝ) (514246569047/1000000000000 : ℝ) (407698824239/500000000000 : ℝ) (163079529699/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0108_exp_lower
  have heNumeric : (2019016637601/1000000000000 : ℝ)/4 ≤ Real.exp (-273473512523/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019016637601/1000000000000 : ℝ)/4 ≤ Real.exp ((1079/8192 : ℝ)-(163079529699/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1079/8192 : ℝ) (2159/16384 : ℝ) (163079529699/200000000000 : ℝ) (2019016637601/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0109; no trusted numerical premise.
theorem cover7_leaf0109_exp_radius : (997648555816826837/1000000000000000000 : ℝ) ≤ Real.exp ((-135/7168 : ℝ)/8) ∧ Real.exp ((-135/7168 : ℝ)/8) ≤ (498824277908413419/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-135/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0109_exp_lower : (918089276024655913/1000000000000000000 : ℝ) ≤ Real.exp ((-2734740560597/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734740560597/4000000000000 : ℝ)/8) ≤ (459044638012327957/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734740560597/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0109_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506947039/500000000000 : ℝ) ≤ 4*Real.exp (2159/16384 : ℝ)*Real.exp (-mu (radius 7 (135/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506947039/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (135/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0109_exp_radius
  have hrNumeric : (981342540681/1000000000000 : ℝ) ≤ Real.exp (-135/7168 : ℝ) ∧ Real.exp (-135/7168 : ℝ) ≤ (490671270341/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981342540681/1000000000000 : ℝ) ≤ (radius 7 (135/1024 : ℝ)) ∧ (radius 7 (135/1024 : ℝ)) ≤ (490671270341/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (135/1024 : ℝ)) (981342540681/1000000000000 : ℝ) (490671270341/500000000000 : ℝ) (48066892093/250000000000 : ℝ) (96133784189/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (135/1024 : ℝ)) (981342540681/1000000000000 : ℝ) (490671270341/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (135/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981342540681/1000000000000 : ℝ) (490671270341/500000000000 : ℝ) (49533563517/50000000000 : ℝ) (990671270341/1000000000000 : ℝ) (247656836757/250000000000 : ℝ) (99062734703/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (135/1024 : ℝ)) 1 (49533563517/50000000000 : ℝ) (990671270341/1000000000000 : ℝ) (247656836757/250000000000 : ℝ) (99062734703/100000000000 : ℝ) (247662327171/250000000000 : ℝ) (495324654343/500000000000 : ℝ) (24766232711/25000000000 : ℝ) (990649308443/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (135/1024 : ℝ)) 2 (247662327171/250000000000 : ℝ) (495324654343/500000000000 : ℝ) (24766232711/25000000000 : ℝ) (990649308443/1000000000000 : ℝ) (495324654281/500000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (135/1024 : ℝ)) 3 (495324654281/500000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (135/1024 : ℝ)) 4 (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (135/1024 : ℝ)) 5 (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (135/1024 : ℝ)) 6 (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (135/1024 : ℝ)) 7 (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (135/1024 : ℝ))) (48066892093/250000000000 : ℝ) (96133784189/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (135/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48066892093/250000000000 : ℝ) (96133784189/500000000000 : ℝ) (298066892093/500000000000 : ℝ) (596133784189/1000000000000 : ℝ) (438483258941/1000000000000 : ℝ) (438483258949/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (135/1024 : ℝ))) 1 (298066892093/500000000000 : ℝ) (596133784189/1000000000000 : ℝ) (438483258941/1000000000000 : ℝ) (438483258949/1000000000000 : ℝ) (517308521563/1000000000000 : ℝ) (517308521569/1000000000000 : ℝ) (4090141783/8000000000 : ℝ) (255633861441/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (135/1024 : ℝ))) 2 (517308521563/1000000000000 : ℝ) (517308521569/1000000000000 : ℝ) (4090141783/8000000000 : ℝ) (255633861441/500000000000 : ℝ) (514288122219/1000000000000 : ℝ) (257144061113/500000000000 : ℝ) (514279252783/1000000000000 : ℝ) (51427925279/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (135/1024 : ℝ))) 3 (514288122219/1000000000000 : ℝ) (257144061113/500000000000 : ℝ) (514279252783/1000000000000 : ℝ) (51427925279/100000000000 : ℝ) (514283687501/1000000000000 : ℝ) (128570921877/250000000000 : ℝ) (514283687481/1000000000000 : ℝ) (514283687489/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (135/1024 : ℝ))) 4 (514283687501/1000000000000 : ℝ) (128570921877/250000000000 : ℝ) (514283687481/1000000000000 : ℝ) (514283687489/1000000000000 : ℝ) (514283687491/1000000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (135/1024 : ℝ))) 5 (514283687491/1000000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (135/1024 : ℝ))) 6 (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (135/1024 : ℝ))) 7 (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (135/1024 : ℝ)) hmem 8 (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (135/1024 : ℝ))) hcmem 8 (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (135/1024 : ℝ)) (990649308561/1000000000000 : ℝ) (198129861713/200000000000 : ℝ) (51428368749/100000000000 : ℝ) (514283687499/1000000000000 : ℝ) (407730021237/500000000000 : ℝ) (815460042493/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0109_exp_lower
  have heNumeric : (1009506947039/500000000000 : ℝ)/4 ≤ Real.exp (-2734740560597/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506947039/500000000000 : ℝ)/4 ≤ Real.exp ((2159/16384 : ℝ)-(815460042493/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2159/16384 : ℝ) (135/1024 : ℝ) (815460042493/1000000000000 : ℝ) (1009506947039/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0110; no trusted numerical premise.
theorem cover7_leaf0110_exp_radius : (498823734233392851/500000000000000000 : ℝ) ≤ Real.exp ((-2161/114688 : ℝ)/8) ∧ Real.exp ((-2161/114688 : ℝ)/8) ≤ (997647468466785703/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2161/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0110_exp_lower : (229522280575674531/250000000000000000 : ℝ) ≤ Real.exp ((-170921619911/250000000000 : ℝ)/8) ∧ Real.exp ((-170921619911/250000000000 : ℝ)/8) ≤ (1468942595684317/1600000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170921619911/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0110_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505594811/500000000000 : ℝ) ≤ 4*Real.exp (135/1024 : ℝ)*Real.exp (-mu (radius 7 (2161/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505594811/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2161/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0110_exp_radius
  have hrNumeric : (981333984091/1000000000000 : ℝ) ≤ Real.exp (-2161/114688 : ℝ) ∧ Real.exp (-2161/114688 : ℝ) ≤ (245333496023/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981333984091/1000000000000 : ℝ) ≤ (radius 7 (2161/16384 : ℝ)) ∧ (radius 7 (2161/16384 : ℝ)) ≤ (245333496023/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2161/16384 : ℝ)) (981333984091/1000000000000 : ℝ) (245333496023/250000000000 : ℝ) (192311236453/1000000000000 : ℝ) (192311236459/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2161/16384 : ℝ)) (981333984091/1000000000000 : ℝ) (245333496023/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2161/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981333984091/1000000000000 : ℝ) (245333496023/250000000000 : ℝ) (198133398409/200000000000 : ℝ) (495333496023/500000000000 : ℝ) (198124605649/200000000000 : ℝ) (990623028247/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2161/16384 : ℝ)) 1 (198133398409/200000000000 : ℝ) (495333496023/500000000000 : ℝ) (198124605649/200000000000 : ℝ) (990623028247/1000000000000 : ℝ) (198129002029/200000000000 : ℝ) (990645010147/1000000000000 : ℝ) (990645009901/1000000000000 : ℝ) (990645009903/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2161/16384 : ℝ)) 2 (198129002029/200000000000 : ℝ) (990645010147/1000000000000 : ℝ) (990645009901/1000000000000 : ℝ) (990645009903/1000000000000 : ℝ) (990645010023/1000000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2161/16384 : ℝ)) 3 (990645010023/1000000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2161/16384 : ℝ)) 4 (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2161/16384 : ℝ)) 5 (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2161/16384 : ℝ)) 6 (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2161/16384 : ℝ)) 7 (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2161/16384 : ℝ))) (192311236453/1000000000000 : ℝ) (192311236459/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2161/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192311236453/1000000000000 : ℝ) (192311236459/1000000000000 : ℝ) (298077809113/500000000000 : ℝ) (59615561823/100000000000 : ℝ) (219266525291/500000000000 : ℝ) (43853305059/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2161/16384 : ℝ))) 1 (298077809113/500000000000 : ℝ) (59615561823/100000000000 : ℝ) (219266525291/500000000000 : ℝ) (43853305059/100000000000 : ℝ) (129336083601/250000000000 : ℝ) (51734433441/100000000000 : ℝ) (20452244547/40000000000 : ℝ) (511306113683/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2161/16384 : ℝ))) 2 (129336083601/250000000000 : ℝ) (51734433441/100000000000 : ℝ) (20452244547/40000000000 : ℝ) (511306113683/1000000000000 : ℝ) (514325224039/1000000000000 : ℝ) (514325224047/1000000000000 : ℝ) (514316362811/1000000000000 : ℝ) (514316362819/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2161/16384 : ℝ))) 3 (514325224039/1000000000000 : ℝ) (514325224047/1000000000000 : ℝ) (514316362811/1000000000000 : ℝ) (514316362819/1000000000000 : ℝ) (20572831737/40000000000 : ℝ) (514320793433/1000000000000 : ℝ) (102864158681/200000000000 : ℝ) (257160396707/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2161/16384 : ℝ))) 4 (20572831737/40000000000 : ℝ) (514320793433/1000000000000 : ℝ) (102864158681/200000000000 : ℝ) (257160396707/500000000000 : ℝ) (102864158683/200000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2161/16384 : ℝ))) 5 (102864158683/200000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2161/16384 : ℝ))) 6 (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2161/16384 : ℝ))) 7 (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2161/16384 : ℝ)) hmem 8 (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2161/16384 : ℝ))) hcmem 8 (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2161/16384 : ℝ)) (495322505011/500000000000 : ℝ) (39625800401/40000000000 : ℝ) (257160396707/500000000000 : ℝ) (32145049589/62500000000 : ℝ) (6524179337/8000000000 : ℝ) (101940302143/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0110_exp_lower
  have heNumeric : (1009505594811/500000000000 : ℝ)/4 ≤ Real.exp (-170921619911/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505594811/500000000000 : ℝ)/4 ≤ Real.exp ((135/1024 : ℝ)-(101940302143/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (135/1024 : ℝ) (2161/16384 : ℝ) (101940302143/125000000000 : ℝ) (1009505594811/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0111; no trusted numerical premise.
theorem cover7_leaf0111_exp_radius : (997646381117929683/1000000000000000000 : ℝ) ≤ Real.exp ((-1081/57344 : ℝ)/8) ∧ Real.exp ((-1081/57344 : ℝ)/8) ≤ (249411595279482421/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1081/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0111_exp_lower : (36723558831913447/40000000000000000 : ℝ) ≤ Real.exp ((-2734751199279/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734751199279/4000000000000 : ℝ)/8) ≤ (57380560674864761/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734751199279/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0111_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009504262087/500000000000 : ℝ) ≤ 4*Real.exp (2161/16384 : ℝ)*Real.exp (-mu (radius 7 (1081/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009504262087/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1081/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0111_exp_radius
  have hrNumeric : (39253017103/40000000000 : ℝ) ≤ Real.exp (-1081/57344 : ℝ) ∧ Real.exp (-1081/57344 : ℝ) ≤ (122665678447/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39253017103/40000000000 : ℝ) ≤ (radius 7 (1081/8192 : ℝ)) ∧ (radius 7 (1081/8192 : ℝ)) ≤ (122665678447/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1081/8192 : ℝ)) (39253017103/40000000000 : ℝ) (122665678447/125000000000 : ℝ) (96177446931/500000000000 : ℝ) (48088723467/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1081/8192 : ℝ)) (39253017103/40000000000 : ℝ) (122665678447/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1081/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39253017103/40000000000 : ℝ) (122665678447/125000000000 : ℝ) (990662713787/1000000000000 : ℝ) (247665678447/250000000000 : ℝ) (990618709481/1000000000000 : ℝ) (990618709483/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1081/8192 : ℝ)) 1 (990662713787/1000000000000 : ℝ) (247665678447/250000000000 : ℝ) (990618709481/1000000000000 : ℝ) (990618709483/1000000000000 : ℝ) (495320355817/500000000000 : ℝ) (247660177909/250000000000 : ℝ) (990640711389/1000000000000 : ℝ) (30957522231/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1081/8192 : ℝ)) 2 (495320355817/500000000000 : ℝ) (247660177909/250000000000 : ℝ) (990640711389/1000000000000 : ℝ) (30957522231/31250000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1081/8192 : ℝ)) 3 (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1081/8192 : ℝ)) 4 (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1081/8192 : ℝ)) 5 (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1081/8192 : ℝ)) 6 (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1081/8192 : ℝ)) 7 (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1081/8192 : ℝ))) (96177446931/500000000000 : ℝ) (48088723467/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1081/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96177446931/500000000000 : ℝ) (48088723467/250000000000 : ℝ) (596177446931/1000000000000 : ℝ) (298088723467/500000000000 : ℝ) (438582824403/1000000000000 : ℝ) (438582824411/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1081/8192 : ℝ))) 1 (596177446931/1000000000000 : ℝ) (298088723467/500000000000 : ℝ) (438582824403/1000000000000 : ℝ) (438582824411/1000000000000 : ℝ) (517380135667/1000000000000 : ℝ) (517380135673/1000000000000 : ℝ) (511344491043/1000000000000 : ℝ) (10226889821/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1081/8192 : ℝ))) 2 (517380135667/1000000000000 : ℝ) (517380135673/1000000000000 : ℝ) (511344491043/1000000000000 : ℝ) (10226889821/20000000000 : ℝ) (102872462671/200000000000 : ℝ) (257181156681/500000000000 : ℝ) (20574138413/40000000000 : ℝ) (128588365083/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1081/8192 : ℝ))) 3 (102872462671/200000000000 : ℝ) (257181156681/500000000000 : ℝ) (20574138413/40000000000 : ℝ) (128588365083/250000000000 : ℝ) (12858947171/25000000000 : ℝ) (514357886847/1000000000000 : ℝ) (25717894341/50000000000 : ℝ) (128589471707/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1081/8192 : ℝ))) 4 (12858947171/25000000000 : ℝ) (514357886847/1000000000000 : ℝ) (25717894341/50000000000 : ℝ) (128589471707/250000000000 : ℝ) (51435788683/100000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1081/8192 : ℝ))) 5 (51435788683/100000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1081/8192 : ℝ))) 6 (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1081/8192 : ℝ))) 7 (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1081/8192 : ℝ)) hmem 8 (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1081/8192 : ℝ))) hcmem 8 (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1081/8192 : ℝ)) (990640711511/1000000000000 : ℝ) (495320355757/500000000000 : ℝ) (514357886829/1000000000000 : ℝ) (257178943419/500000000000 : ℝ) (815584772459/1000000000000 : ℝ) (203896193119/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0111_exp_lower
  have heNumeric : (1009504262087/500000000000 : ℝ)/4 ≤ Real.exp (-2734751199279/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009504262087/500000000000 : ℝ)/4 ≤ Real.exp ((2161/16384 : ℝ)-(203896193119/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2161/16384 : ℝ) (1081/8192 : ℝ) (203896193119/250000000000 : ℝ) (1009504262087/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0112; no trusted numerical premise.
theorem cover7_leaf0112_exp_radius : (49882264688512939/50000000000000000 : ℝ) ≤ Real.exp ((-309/16384 : ℝ)/8) ∧ Real.exp ((-309/16384 : ℝ)/8) ≤ (997645293770258781/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-309/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0112_exp_lower : (459044410753944253/500000000000000000 : ℝ) ≤ Real.exp ((-1367378201391/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367378201391/2000000000000 : ℝ)/8) ≤ (918088821507888507/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367378201391/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0112_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (63093934303/31250000000 : ℝ) ≤ 4*Real.exp (1081/8192 : ℝ)*Real.exp (-mu (radius 7 (2163/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (63093934303/31250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2163/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0112_exp_radius
  have hrNumeric : (981316871133/1000000000000 : ℝ) ≤ Real.exp (-309/16384 : ℝ) ∧ Real.exp (-309/16384 : ℝ) ≤ (490658435567/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981316871133/1000000000000 : ℝ) ≤ (radius 7 (2163/16384 : ℝ)) ∧ (radius 7 (2163/16384 : ℝ)) ≤ (490658435567/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2163/16384 : ℝ)) (981316871133/1000000000000 : ℝ) (490658435567/500000000000 : ℝ) (192398540607/1000000000000 : ℝ) (192398540613/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2163/16384 : ℝ)) (981316871133/1000000000000 : ℝ) (490658435567/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2163/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981316871133/1000000000000 : ℝ) (490658435567/500000000000 : ℝ) (495329217783/500000000000 : ℝ) (990658435567/1000000000000 : ℝ) (198122878147/200000000000 : ℝ) (990614390737/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2163/16384 : ℝ)) 1 (495329217783/500000000000 : ℝ) (990658435567/1000000000000 : ℝ) (198122878147/200000000000 : ℝ) (990614390737/1000000000000 : ℝ) (19812728263/20000000000 : ℝ) (30957387911/31250000000 : ℝ) (198127282581/200000000000 : ℝ) (247659103227/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2163/16384 : ℝ)) 2 (19812728263/20000000000 : ℝ) (30957387911/31250000000 : ℝ) (198127282581/200000000000 : ℝ) (247659103227/250000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2163/16384 : ℝ)) 3 (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2163/16384 : ℝ)) 4 (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2163/16384 : ℝ)) 5 (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2163/16384 : ℝ)) 6 (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2163/16384 : ℝ)) 7 (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2163/16384 : ℝ))) (192398540607/1000000000000 : ℝ) (192398540613/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2163/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192398540607/1000000000000 : ℝ) (192398540613/1000000000000 : ℝ) (596199270303/1000000000000 : ℝ) (596199270307/1000000000000 : ℝ) (438632580421/1000000000000 : ℝ) (438632580429/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2163/16384 : ℝ))) 1 (596199270303/1000000000000 : ℝ) (596199270307/1000000000000 : ℝ) (438632580421/1000000000000 : ℝ) (438632580429/1000000000000 : ℝ) (258707962681/500000000000 : ℝ) (64676990671/125000000000 : ℝ) (51138285499/100000000000 : ℝ) (511382854997/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2163/16384 : ℝ))) 2 (258707962681/500000000000 : ℝ) (64676990671/125000000000 : ℝ) (51138285499/100000000000 : ℝ) (511382854997/1000000000000 : ℝ) (16074980943/31250000000 : ℝ) (514399390183/1000000000000 : ℝ) (514390545333/1000000000000 : ℝ) (514390545341/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2163/16384 : ℝ))) 3 (16074980943/31250000000 : ℝ) (514399390183/1000000000000 : ℝ) (514390545333/1000000000000 : ℝ) (514390545341/1000000000000 : ℝ) (257197483877/500000000000 : ℝ) (257197483881/500000000000 : ℝ) (102878993547/200000000000 : ℝ) (514394967743/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2163/16384 : ℝ))) 4 (257197483877/500000000000 : ℝ) (257197483881/500000000000 : ℝ) (102878993547/200000000000 : ℝ) (514394967743/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2163/16384 : ℝ))) 5 (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2163/16384 : ℝ))) 6 (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2163/16384 : ℝ))) 7 (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2163/16384 : ℝ)) hmem 8 (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2163/16384 : ℝ))) hcmem 8 (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2163/16384 : ℝ)) (990636413027/1000000000000 : ℝ) (99063641303/100000000000 : ℝ) (8037421371/15625000000 : ℝ) (514394967753/1000000000000 : ℝ) (815647108491/1000000000000 : ℝ) (203911777127/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0112_exp_lower
  have heNumeric : (63093934303/31250000000 : ℝ)/4 ≤ Real.exp (-1367378201391/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (63093934303/31250000000 : ℝ)/4 ≤ Real.exp ((1081/8192 : ℝ)-(203911777127/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1081/8192 : ℝ) (2163/16384 : ℝ) (203911777127/250000000000 : ℝ) (63093934303/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0113; no trusted numerical premise.
theorem cover7_leaf0113_exp_radius : (15588190725371453/15625000000000000 : ℝ) ≤ Real.exp ((-541/28672 : ℝ)/8) ∧ Real.exp ((-541/28672 : ℝ)/8) ≤ (997644206423772993/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-541/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0113_exp_lower : (918088674432968799/1000000000000000000 : ℝ) ≤ Real.exp ((-2734761529081/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734761529081/4000000000000 : ℝ)/8) ≤ (1147610843041211/1250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734761529081/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0113_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019003310191/1000000000000 : ℝ) ≤ 4*Real.exp (2163/16384 : ℝ)*Real.exp (-mu (radius 7 (541/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (2019003310191/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (541/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0113_exp_radius
  have hrNumeric : (981308314767/1000000000000 : ℝ) ≤ Real.exp (-541/28672 : ℝ) ∧ Real.exp (-541/28672 : ℝ) ≤ (61331769673/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981308314767/1000000000000 : ℝ) ≤ (radius 7 (541/4096 : ℝ)) ∧ (radius 7 (541/4096 : ℝ)) ≤ (61331769673/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (541/4096 : ℝ)) (981308314767/1000000000000 : ℝ) (61331769673/62500000000 : ℝ) (48110544171/250000000000 : ℝ) (19244217669/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (541/4096 : ℝ)) (981308314767/1000000000000 : ℝ) (61331769673/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (541/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981308314767/1000000000000 : ℝ) (61331769673/62500000000 : ℝ) (990654157383/1000000000000 : ℝ) (123831769673/125000000000 : ℝ) (990610072009/1000000000000 : ℝ) (990610072011/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (541/4096 : ℝ)) 1 (990654157383/1000000000000 : ℝ) (123831769673/125000000000 : ℝ) (990610072009/1000000000000 : ℝ) (990610072011/1000000000000 : ℝ) (123829014337/125000000000 : ℝ) (495316057349/500000000000 : ℝ) (19812642289/20000000000 : ℝ) (990632114453/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (541/4096 : ℝ)) 2 (123829014337/125000000000 : ℝ) (495316057349/500000000000 : ℝ) (19812642289/20000000000 : ℝ) (990632114453/1000000000000 : ℝ) (990632114573/1000000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (541/4096 : ℝ)) 3 (990632114573/1000000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (541/4096 : ℝ)) 4 (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (541/4096 : ℝ)) 5 (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (541/4096 : ℝ)) 6 (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (541/4096 : ℝ)) 7 (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (541/4096 : ℝ))) (48110544171/250000000000 : ℝ) (19244217669/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (541/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48110544171/250000000000 : ℝ) (19244217669/100000000000 : ℝ) (298110544171/500000000000 : ℝ) (119244217669/200000000000 : ℝ) (109670579659/250000000000 : ℝ) (109670579661/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (541/4096 : ℝ))) 1 (298110544171/500000000000 : ℝ) (119244217669/200000000000 : ℝ) (109670579659/250000000000 : ℝ) (109670579661/250000000000 : ℝ) (517451703489/1000000000000 : ℝ) (103490340699/200000000000 : ℝ) (255710602759/500000000000 : ℝ) (20456848221/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (541/4096 : ℝ))) 2 (517451703489/1000000000000 : ℝ) (103490340699/200000000000 : ℝ) (255710602759/500000000000 : ℝ) (20456848221/40000000000 : ℝ) (514436454503/1000000000000 : ℝ) (51443645451/100000000000 : ℝ) (514427617839/1000000000000 : ℝ) (257213808923/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (541/4096 : ℝ))) 3 (514436454503/1000000000000 : ℝ) (51443645451/100000000000 : ℝ) (514427617839/1000000000000 : ℝ) (257213808923/500000000000 : ℝ) (514432036171/1000000000000 : ℝ) (257216018089/500000000000 : ℝ) (64304004519/125000000000 : ℝ) (1607600113/3125000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (541/4096 : ℝ))) 4 (514432036171/1000000000000 : ℝ) (257216018089/500000000000 : ℝ) (64304004519/125000000000 : ℝ) (1607600113/3125000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (541/4096 : ℝ))) 5 (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (541/4096 : ℝ))) 6 (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (541/4096 : ℝ))) 7 (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (541/4096 : ℝ)) hmem 8 (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (541/4096 : ℝ))) hcmem 8 (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (541/4096 : ℝ)) (247658028643/250000000000 : ℝ) (61914507161/62500000000 : ℝ) (514432036161/1000000000000 : ℝ) (514432036169/1000000000000 : ℝ) (407854712611/500000000000 : ℝ) (815709425239/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0113_exp_lower
  have heNumeric : (2019003310191/1000000000000 : ℝ)/4 ≤ Real.exp (-2734761529081/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019003310191/1000000000000 : ℝ)/4 ≤ Real.exp ((2163/16384 : ℝ)-(815709425239/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2163/16384 : ℝ) (541/4096 : ℝ) (815709425239/1000000000000 : ℝ) (2019003310191/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0114; no trusted numerical premise.
theorem cover7_leaf0114_exp_radius : (249410779769618079/250000000000000000 : ℝ) ≤ Real.exp ((-2165/114688 : ℝ)/8) ∧ Real.exp ((-2165/114688 : ℝ)/8) ≤ (997643119078472317/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2165/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0114_exp_lower : (91808852956894459/100000000000000000 : ℝ) ≤ Real.exp ((-34184582229/50000000000 : ℝ)/8) ∧ Real.exp ((-34184582229/50000000000 : ℝ)/8) ≤ (918088529568944591/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-34184582229/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0114_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403800152317/200000000000 : ℝ) ≤ 4*Real.exp (541/4096 : ℝ)*Real.exp (-mu (radius 7 (2165/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (403800152317/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2165/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0114_exp_radius
  have hrNumeric : (490649879237/500000000000 : ℝ) ≤ Real.exp (-2165/114688 : ℝ) ∧ Real.exp (-2165/114688 : ℝ) ≤ (39251990339/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490649879237/500000000000 : ℝ) ≤ (radius 7 (2165/16384 : ℝ)) ∧ (radius 7 (2165/16384 : ℝ)) ≤ (39251990339/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2165/16384 : ℝ)) (490649879237/500000000000 : ℝ) (39251990339/40000000000 : ℝ) (192485802117/1000000000000 : ℝ) (192485802123/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2165/16384 : ℝ)) (490649879237/500000000000 : ℝ) (39251990339/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2165/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490649879237/500000000000 : ℝ) (39251990339/40000000000 : ℝ) (990649879237/1000000000000 : ℝ) (495324939619/500000000000 : ℝ) (990605753301/1000000000000 : ℝ) (495302876651/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2165/16384 : ℝ)) 1 (990649879237/1000000000000 : ℝ) (495324939619/500000000000 : ℝ) (990605753301/1000000000000 : ℝ) (495302876651/500000000000 : ℝ) (990627816269/1000000000000 : ℝ) (99062781627/100000000000 : ℝ) (990627816023/1000000000000 : ℝ) (39625112641/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2165/16384 : ℝ)) 2 (990627816269/1000000000000 : ℝ) (99062781627/100000000000 : ℝ) (990627816023/1000000000000 : ℝ) (39625112641/40000000000 : ℝ) (495313908073/500000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2165/16384 : ℝ)) 3 (495313908073/500000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2165/16384 : ℝ)) 4 (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2165/16384 : ℝ)) 5 (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2165/16384 : ℝ)) 6 (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2165/16384 : ℝ)) 7 (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2165/16384 : ℝ))) (192485802117/1000000000000 : ℝ) (192485802123/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2165/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192485802117/1000000000000 : ℝ) (192485802123/1000000000000 : ℝ) (298121450529/500000000000 : ℝ) (298121450531/500000000000 : ℝ) (438732039081/1000000000000 : ℝ) (438732039089/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2165/16384 : ℝ))) 1 (298121450529/500000000000 : ℝ) (298121450531/500000000000 : ℝ) (438732039081/1000000000000 : ℝ) (438732039089/1000000000000 : ℝ) (517487470069/1000000000000 : ℝ) (129371867519/250000000000 : ℝ) (10229190853/20000000000 : ℝ) (255729771329/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2165/16384 : ℝ))) 2 (517487470069/1000000000000 : ℝ) (129371867519/250000000000 : ℝ) (10229190853/20000000000 : ℝ) (255729771329/500000000000 : ℝ) (514473506359/1000000000000 : ℝ) (514473506367/1000000000000 : ℝ) (257232338931/500000000000 : ℝ) (514464677871/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2165/16384 : ℝ))) 3 (514473506359/1000000000000 : ℝ) (514473506367/1000000000000 : ℝ) (257232338931/500000000000 : ℝ) (514464677871/1000000000000 : ℝ) (51446909211/100000000000 : ℝ) (514469092119/1000000000000 : ℝ) (514469092091/1000000000000 : ℝ) (514469092101/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2165/16384 : ℝ))) 4 (51446909211/100000000000 : ℝ) (514469092119/1000000000000 : ℝ) (514469092091/1000000000000 : ℝ) (514469092101/1000000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2165/16384 : ℝ))) 5 (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2165/16384 : ℝ))) 6 (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2165/16384 : ℝ))) 7 (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2165/16384 : ℝ)) hmem 8 (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2165/16384 : ℝ))) hcmem 8 (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2165/16384 : ℝ)) (198125563229/200000000000 : ℝ) (247656954037/250000000000 : ℝ) (5144690921/10000000000 : ℝ) (51446909211/100000000000 : ℝ) (407885861343/500000000000 : ℝ) (163154344541/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0114_exp_lower
  have heNumeric : (403800152317/200000000000 : ℝ)/4 ≤ Real.exp (-34184582229/50000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403800152317/200000000000 : ℝ)/4 ≤ Real.exp ((541/4096 : ℝ)-(163154344541/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (541/4096 : ℝ) (2165/16384 : ℝ) (163154344541/200000000000 : ℝ) (403800152317/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0115; no trusted numerical premise.
theorem cover7_leaf0115_exp_radius : (199528515081253279/200000000000000000 : ℝ) ≤ Real.exp ((-4331/229376 : ℝ)/8) ∧ Real.exp ((-4331/229376 : ℝ)/8) ≤ (249410643851566599/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4331/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0115_exp_lower : (459045980101149941/500000000000000000 : ℝ) ≤ Real.exp ((-2734647003727/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734647003727/4000000000000 : ℝ)/8) ≤ (918091960202299883/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734647003727/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0115_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009530558893/500000000000 : ℝ) ≤ 4*Real.exp (2165/16384 : ℝ)*Real.exp (-mu (radius 7 (4331/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009530558893/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4331/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0115_exp_radius
  have hrNumeric : (245323870089/250000000000 : ℝ) ≤ Real.exp (-4331/229376 : ℝ) ∧ Real.exp (-4331/229376 : ℝ) ≤ (981295480357/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245323870089/250000000000 : ℝ) ≤ (radius 7 (4331/32768 : ℝ)) ∧ (radius 7 (4331/32768 : ℝ)) ≤ (981295480357/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4331/32768 : ℝ)) (245323870089/250000000000 : ℝ) (981295480357/1000000000000 : ℝ) (96253805419/500000000000 : ℝ) (38501522169/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4331/32768 : ℝ)) (245323870089/250000000000 : ℝ) (981295480357/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4331/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245323870089/250000000000 : ℝ) (981295480357/1000000000000 : ℝ) (495323870089/500000000000 : ℝ) (990647740179/1000000000000 : ℝ) (495301796977/500000000000 : ℝ) (247650898489/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4331/32768 : ℝ)) 1 (495323870089/500000000000 : ℝ) (990647740179/1000000000000 : ℝ) (495301796977/500000000000 : ℝ) (247650898489/250000000000 : ℝ) (495312833533/500000000000 : ℝ) (247656416767/250000000000 : ℝ) (49531283341/50000000000 : ℝ) (495312833411/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4331/32768 : ℝ)) 2 (495312833533/500000000000 : ℝ) (247656416767/250000000000 : ℝ) (49531283341/50000000000 : ℝ) (495312833411/500000000000 : ℝ) (990625666943/1000000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4331/32768 : ℝ)) 3 (990625666943/1000000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4331/32768 : ℝ)) 4 (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4331/32768 : ℝ)) 5 (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4331/32768 : ℝ)) 6 (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4331/32768 : ℝ)) 7 (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4331/32768 : ℝ))) (96253805419/500000000000 : ℝ) (38501522169/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4331/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96253805419/500000000000 : ℝ) (38501522169/200000000000 : ℝ) (596253805419/1000000000000 : ℝ) (596253805423/1000000000000 : ℝ) (219378446319/500000000000 : ℝ) (438756892647/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4331/32768 : ℝ))) 1 (596253805419/1000000000000 : ℝ) (596253805423/1000000000000 : ℝ) (219378446319/500000000000 : ℝ) (438756892647/1000000000000 : ℝ) (129376337257/250000000000 : ℝ) (103501069807/200000000000 : ℝ) (511478706193/1000000000000 : ℝ) (511478706201/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4331/32768 : ℝ))) 2 (129376337257/250000000000 : ℝ) (103501069807/200000000000 : ℝ) (511478706193/1000000000000 : ℝ) (511478706201/1000000000000 : ℝ) (51449202761/100000000000 : ℝ) (257246013809/500000000000 : ℝ) (257241601597/500000000000 : ℝ) (257241601601/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4331/32768 : ℝ))) 3 (51449202761/100000000000 : ℝ) (257246013809/500000000000 : ℝ) (257241601597/500000000000 : ℝ) (257241601601/500000000000 : ℝ) (257243807701/500000000000 : ℝ) (51448761541/100000000000 : ℝ) (514487615383/1000000000000 : ℝ) (16077737981/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4331/32768 : ℝ))) 4 (257243807701/500000000000 : ℝ) (51448761541/100000000000 : ℝ) (514487615383/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4331/32768 : ℝ))) 5 (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4331/32768 : ℝ))) 6 (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4331/32768 : ℝ))) 7 (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4331/32768 : ℝ)) hmem 8 (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4331/32768 : ℝ))) hcmem 8 (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4331/32768 : ℝ)) (495312833471/500000000000 : ℝ) (198125133389/200000000000 : ℝ) (16077737981/31250000000 : ℝ) (514487615401/1000000000000 : ℝ) (163160572839/200000000000 : ℝ) (815802864213/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0115_exp_lower
  have heNumeric : (1009530558893/500000000000 : ℝ)/4 ≤ Real.exp (-2734647003727/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009530558893/500000000000 : ℝ)/4 ≤ Real.exp ((2165/16384 : ℝ)-(815802864213/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2165/16384 : ℝ) (4331/32768 : ℝ) (815802864213/1000000000000 : ℝ) (1009530558893/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0116; no trusted numerical premise.
theorem cover7_leaf0116_exp_radius : (62352626983397297/62500000000000000 : ℝ) ≤ Real.exp ((-1083/57344 : ℝ)/8) ∧ Real.exp ((-1083/57344 : ℝ)/8) ≤ (997642031734356753/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1083/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0116_exp_lower : (183618377830373749/200000000000000000 : ℝ) ≤ Real.exp ((-1093859792073/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093859792073/1600000000000 : ℝ)/8) ≤ (459045944575934373/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093859792073/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0116_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019059867757/1000000000000 : ℝ) ≤ 4*Real.exp (4331/32768 : ℝ)*Real.exp (-mu (radius 7 (1083/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019059867757/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1083/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0116_exp_radius
  have hrNumeric : (981291202257/1000000000000 : ℝ) ≤ Real.exp (-1083/57344 : ℝ) ∧ Real.exp (-1083/57344 : ℝ) ≤ (490645601129/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981291202257/1000000000000 : ℝ) ≤ (radius 7 (1083/8192 : ℝ)) ∧ (radius 7 (1083/8192 : ℝ)) ≤ (490645601129/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1083/8192 : ℝ)) (981291202257/1000000000000 : ℝ) (490645601129/500000000000 : ℝ) (192529416897/1000000000000 : ℝ) (24066177113/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1083/8192 : ℝ)) (981291202257/1000000000000 : ℝ) (490645601129/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1083/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981291202257/1000000000000 : ℝ) (490645601129/500000000000 : ℝ) (123830700141/125000000000 : ℝ) (990645601129/1000000000000 : ℝ) (247650358653/250000000000 : ℝ) (495300717307/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1083/8192 : ℝ)) 1 (123830700141/125000000000 : ℝ) (990645601129/1000000000000 : ℝ) (247650358653/250000000000 : ℝ) (495300717307/500000000000 : ℝ) (99062351787/100000000000 : ℝ) (61913969867/62500000000 : ℝ) (990623517623/1000000000000 : ℝ) (495311758813/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1083/8192 : ℝ)) 2 (99062351787/100000000000 : ℝ) (61913969867/62500000000 : ℝ) (990623517623/1000000000000 : ℝ) (495311758813/500000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1083/8192 : ℝ)) 3 (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1083/8192 : ℝ)) 4 (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1083/8192 : ℝ)) 5 (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1083/8192 : ℝ)) 6 (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1083/8192 : ℝ)) 7 (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1083/8192 : ℝ))) (192529416897/1000000000000 : ℝ) (24066177113/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1083/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192529416897/1000000000000 : ℝ) (24066177113/125000000000 : ℝ) (18633272139/31250000000 : ℝ) (149066177113/250000000000 : ℝ) (219390870877/500000000000 : ℝ) (438781741763/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1083/8192 : ℝ))) 1 (18633272139/31250000000 : ℝ) (149066177113/250000000000 : ℝ) (219390870877/500000000000 : ℝ) (438781741763/1000000000000 : ℝ) (517523225101/1000000000000 : ℝ) (129380806277/250000000000 : ℝ) (511497866387/1000000000000 : ℝ) (102299573279/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1083/8192 : ℝ))) 2 (517523225101/1000000000000 : ℝ) (129380806277/250000000000 : ℝ) (511497866387/1000000000000 : ℝ) (102299573279/200000000000 : ℝ) (32156909109/62500000000 : ℝ) (64313818219/125000000000 : ℝ) (102900345081/200000000000 : ℝ) (514501725413/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1083/8192 : ℝ))) 3 (32156909109/62500000000 : ℝ) (64313818219/125000000000 : ℝ) (102900345081/200000000000 : ℝ) (514501725413/1000000000000 : ℝ) (257253067787/500000000000 : ℝ) (514506135583/1000000000000 : ℝ) (102901227111/200000000000 : ℝ) (128626533891/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1083/8192 : ℝ))) 4 (257253067787/500000000000 : ℝ) (514506135583/1000000000000 : ℝ) (102901227111/200000000000 : ℝ) (128626533891/250000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1083/8192 : ℝ))) 5 (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1083/8192 : ℝ))) 6 (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1083/8192 : ℝ))) 7 (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1083/8192 : ℝ)) hmem 8 (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1083/8192 : ℝ))) hcmem 8 (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1083/8192 : ℝ)) (495311758873/500000000000 : ℝ) (990623517749/1000000000000 : ℝ) (128626533891/250000000000 : ℝ) (257253067787/500000000000 : ℝ) (407917000443/500000000000 : ℝ) (163166800181/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0116_exp_lower
  have heNumeric : (2019059867757/1000000000000 : ℝ)/4 ≤ Real.exp (-1093859792073/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019059867757/1000000000000 : ℝ)/4 ≤ Real.exp ((4331/32768 : ℝ)-(163166800181/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4331/32768 : ℝ) (1083/8192 : ℝ) (163166800181/200000000000 : ℝ) (2019059867757/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0117; no trusted numerical premise.
theorem cover7_leaf0117_exp_radius : (997641488062743387/1000000000000000000 : ℝ) ≤ Real.exp ((-619/32768 : ℝ)/8) ∧ Real.exp ((-619/32768 : ℝ)/8) ≤ (249410372015685847/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-619/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0117_exp_lower : (91809181865321629/100000000000000000 : ℝ) ≤ Real.exp ((-1367325968703/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367325968703/2000000000000 : ℝ)/8) ≤ (918091818653216291/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367325968703/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0117_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019058627437/1000000000000 : ℝ) ≤ 4*Real.exp (1083/8192 : ℝ)*Real.exp (-mu (radius 7 (4333/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019058627437/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4333/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0117_exp_radius
  have hrNumeric : (61330432761/62500000000 : ℝ) ≤ Real.exp (-619/32768 : ℝ) ∧ Real.exp (-619/32768 : ℝ) ≤ (981286924177/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61330432761/62500000000 : ℝ) ≤ (radius 7 (4333/32768 : ℝ)) ∧ (radius 7 (4333/32768 : ℝ)) ≤ (981286924177/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4333/32768 : ℝ)) (61330432761/62500000000 : ℝ) (981286924177/1000000000000 : ℝ) (1925512203/10000000000 : ℝ) (96275610153/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4333/32768 : ℝ)) (61330432761/62500000000 : ℝ) (981286924177/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4333/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61330432761/62500000000 : ℝ) (981286924177/1000000000000 : ℝ) (123830432761/125000000000 : ℝ) (990643462089/1000000000000 : ℝ) (39623971011/40000000000 : ℝ) (247649818819/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4333/32768 : ℝ)) 1 (123830432761/125000000000 : ℝ) (990643462089/1000000000000 : ℝ) (39623971011/40000000000 : ℝ) (247649818819/250000000000 : ℝ) (990621368681/1000000000000 : ℝ) (990621368683/1000000000000 : ℝ) (198124273687/200000000000 : ℝ) (990621368437/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4333/32768 : ℝ)) 2 (990621368681/1000000000000 : ℝ) (990621368683/1000000000000 : ℝ) (198124273687/200000000000 : ℝ) (990621368437/1000000000000 : ℝ) (495310684279/500000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4333/32768 : ℝ)) 3 (495310684279/500000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4333/32768 : ℝ)) 4 (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4333/32768 : ℝ)) 5 (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4333/32768 : ℝ)) 6 (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4333/32768 : ℝ)) 7 (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4333/32768 : ℝ))) (1925512203/10000000000 : ℝ) (96275610153/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4333/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1925512203/10000000000 : ℝ) (96275610153/500000000000 : ℝ) (11925512203/20000000000 : ℝ) (596275610153/1000000000000 : ℝ) (109701646609/250000000000 : ℝ) (109701646611/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4333/32768 : ℝ))) 1 (11925512203/20000000000 : ℝ) (596275610153/1000000000000 : ℝ) (109701646609/250000000000 : ℝ) (109701646611/250000000000 : ℝ) (517541098293/1000000000000 : ℝ) (517541098299/1000000000000 : ℝ) (12787925581/25000000000 : ℝ) (511517023247/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4333/32768 : ℝ))) 2 (517541098293/1000000000000 : ℝ) (517541098299/1000000000000 : ℝ) (12787925581/25000000000 : ℝ) (511517023247/1000000000000 : ℝ) (257264530383/500000000000 : ℝ) (514529060773/1000000000000 : ℝ) (257260122251/500000000000 : ℝ) (51452024451/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4333/32768 : ℝ))) 3 (257264530383/500000000000 : ℝ) (514529060773/1000000000000 : ℝ) (257260122251/500000000000 : ℝ) (51452024451/100000000000 : ℝ) (257262326317/500000000000 : ℝ) (257262326321/500000000000 : ℝ) (102904930523/200000000000 : ℝ) (514524652623/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4333/32768 : ℝ))) 4 (257262326317/500000000000 : ℝ) (257262326321/500000000000 : ℝ) (102904930523/200000000000 : ℝ) (514524652623/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4333/32768 : ℝ))) 5 (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4333/32768 : ℝ))) 6 (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4333/32768 : ℝ))) 7 (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4333/32768 : ℝ)) hmem 8 (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4333/32768 : ℝ))) hcmem 8 (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4333/32768 : ℝ)) (990621368557/1000000000000 : ℝ) (12382767107/12500000000 : ℝ) (32157790789/62500000000 : ℝ) (514524652633/1000000000000 : ℝ) (203966283193/250000000000 : ℝ) (815865132789/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0117_exp_lower
  have heNumeric : (2019058627437/1000000000000 : ℝ)/4 ≤ Real.exp (-1367325968703/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019058627437/1000000000000 : ℝ)/4 ≤ Real.exp ((1083/8192 : ℝ)-(815865132789/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1083/8192 : ℝ) (4333/32768 : ℝ) (815865132789/1000000000000 : ℝ) (2019058627437/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0118; no trusted numerical premise.
theorem cover7_leaf0118_exp_radius : (997640944391426299/1000000000000000000 : ℝ) ≤ Real.exp ((-2167/114688 : ℝ)/8) ∧ Real.exp ((-2167/114688 : ℝ)/8) ≤ (9976409443914263/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2167/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0118_exp_lower : (918091748706686673/1000000000000000000 : ℝ) ≤ Real.exp ((-5469308750771/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469308750771/8000000000000 : ℝ)/8) ≤ (459045874353343337/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469308750771/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0118_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (63095543651/31250000000 : ℝ) ≤ 4*Real.exp (4333/32768 : ℝ)*Real.exp (-mu (radius 7 (2167/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (63095543651/31250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2167/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0118_exp_radius
  have hrNumeric : (490641323057/500000000000 : ℝ) ≤ Real.exp (-2167/114688 : ℝ) ∧ Real.exp (-2167/114688 : ℝ) ≤ (196256529223/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490641323057/500000000000 : ℝ) ≤ (radius 7 (2167/16384 : ℝ)) ∧ (radius 7 (2167/16384 : ℝ)) ≤ (196256529223/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2167/16384 : ℝ)) (490641323057/500000000000 : ℝ) (196256529223/200000000000 : ℝ) (96286510521/500000000000 : ℝ) (24071627631/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2167/16384 : ℝ)) (490641323057/500000000000 : ℝ) (196256529223/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2167/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490641323057/500000000000 : ℝ) (196256529223/200000000000 : ℝ) (990641323057/1000000000000 : ℝ) (495320661529/500000000000 : ℝ) (495298557971/500000000000 : ℝ) (123824639493/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2167/16384 : ℝ)) 1 (990641323057/1000000000000 : ℝ) (495320661529/500000000000 : ℝ) (495298557971/500000000000 : ℝ) (123824639493/125000000000 : ℝ) (990619219499/1000000000000 : ℝ) (990619219501/1000000000000 : ℝ) (247654804813/250000000000 : ℝ) (198123843851/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2167/16384 : ℝ)) 2 (990619219499/1000000000000 : ℝ) (990619219501/1000000000000 : ℝ) (247654804813/250000000000 : ℝ) (198123843851/200000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2167/16384 : ℝ)) 3 (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2167/16384 : ℝ)) 4 (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2167/16384 : ℝ)) 5 (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2167/16384 : ℝ)) 6 (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2167/16384 : ℝ)) 7 (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2167/16384 : ℝ))) (96286510521/500000000000 : ℝ) (24071627631/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2167/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96286510521/500000000000 : ℝ) (24071627631/125000000000 : ℝ) (596286510521/1000000000000 : ℝ) (149071627631/250000000000 : ℝ) (438831426679/1000000000000 : ℝ) (438831426687/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2167/16384 : ℝ))) 1 (596286510521/1000000000000 : ℝ) (149071627631/250000000000 : ℝ) (438831426679/1000000000000 : ℝ) (438831426687/1000000000000 : ℝ) (2587794843/5000000000 : ℝ) (258779484303/500000000000 : ℝ) (511536176747/1000000000000 : ℝ) (255768088377/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2167/16384 : ℝ))) 2 (2587794843/5000000000 : ℝ) (258779484303/500000000000 : ℝ) (511536176747/1000000000000 : ℝ) (255768088377/500000000000 : ℝ) (514547572673/1000000000000 : ℝ) (12863689317/25000000000 : ℝ) (257269380241/500000000000 : ℝ) (514538760489/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2167/16384 : ℝ))) 3 (514547572673/1000000000000 : ℝ) (12863689317/25000000000 : ℝ) (257269380241/500000000000 : ℝ) (514538760489/1000000000000 : ℝ) (514543166577/1000000000000 : ℝ) (102908633317/200000000000 : ℝ) (257271583279/500000000000 : ℝ) (257271583283/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2167/16384 : ℝ))) 4 (514543166577/1000000000000 : ℝ) (102908633317/200000000000 : ℝ) (257271583279/500000000000 : ℝ) (257271583283/500000000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2167/16384 : ℝ))) 5 (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2167/16384 : ℝ))) 6 (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2167/16384 : ℝ))) 7 (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2167/16384 : ℝ)) hmem 8 (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2167/16384 : ℝ))) hcmem 8 (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2167/16384 : ℝ)) (1584990751/1600000000 : ℝ) (495309609689/500000000000 : ℝ) (514543166567/1000000000000 : ℝ) (32158947911/62500000000 : ℝ) (203974064961/250000000000 : ℝ) (407948129931/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0118_exp_lower
  have heNumeric : (63095543651/31250000000 : ℝ)/4 ≤ Real.exp (-5469308750771/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (63095543651/31250000000 : ℝ)/4 ≤ Real.exp ((4333/32768 : ℝ)-(407948129931/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4333/32768 : ℝ) (2167/16384 : ℝ) (407948129931/500000000000 : ℝ) (63095543651/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0119; no trusted numerical premise.
theorem cover7_leaf0119_exp_radius : (62352525045025343/62500000000000000 : ℝ) ≤ Real.exp ((-4335/229376 : ℝ)/8) ∧ Real.exp ((-4335/229376 : ℝ)/8) ≤ (997640400720405489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4335/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0119_exp_lower : (183618335862226431/200000000000000000 : ℝ) ≤ Real.exp ((-2734656794161/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734656794161/4000000000000 : ℝ)/8) ≤ (229522919827783039/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734656794161/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0119_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019056175921/1000000000000 : ℝ) ≤ 4*Real.exp (2167/16384 : ℝ)*Real.exp (-mu (radius 7 (4335/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019056175921/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4335/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0119_exp_radius
  have hrNumeric : (98127836807/100000000000 : ℝ) ≤ Real.exp (-4335/229376 : ℝ) ∧ Real.exp (-4335/229376 : ℝ) ≤ (981278368071/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98127836807/100000000000 : ℝ) ≤ (radius 7 (4335/32768 : ℝ)) ∧ (radius 7 (4335/32768 : ℝ)) ≤ (981278368071/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4335/32768 : ℝ)) (98127836807/100000000000 : ℝ) (981278368071/1000000000000 : ℝ) (19259481913/100000000000 : ℝ) (3009294049/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4335/32768 : ℝ)) (98127836807/100000000000 : ℝ) (981278368071/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4335/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98127836807/100000000000 : ℝ) (981278368071/1000000000000 : ℝ) (198127836807/200000000000 : ℝ) (247659796009/250000000000 : ℝ) (495297478307/500000000000 : ℝ) (198118991323/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4335/32768 : ℝ)) 1 (198127836807/200000000000 : ℝ) (247659796009/250000000000 : ℝ) (495297478307/500000000000 : ℝ) (198118991323/200000000000 : ℝ) (247654267581/250000000000 : ℝ) (495308535163/500000000000 : ℝ) (990617070077/1000000000000 : ℝ) (990617070079/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4335/32768 : ℝ)) 2 (247654267581/250000000000 : ℝ) (495308535163/500000000000 : ℝ) (990617070077/1000000000000 : ℝ) (990617070079/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4335/32768 : ℝ)) 3 (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4335/32768 : ℝ)) 4 (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4335/32768 : ℝ)) 5 (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4335/32768 : ℝ)) 6 (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4335/32768 : ℝ)) 7 (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4335/32768 : ℝ))) (19259481913/100000000000 : ℝ) (3009294049/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4335/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19259481913/100000000000 : ℝ) (3009294049/15625000000 : ℝ) (119259481913/200000000000 : ℝ) (18634294049/31250000000 : ℝ) (438856262493/1000000000000 : ℝ) (438856262501/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4335/32768 : ℝ))) 1 (119259481913/200000000000 : ℝ) (18634294049/31250000000 : ℝ) (438856262493/1000000000000 : ℝ) (438856262501/1000000000000 : ℝ) (517576836029/1000000000000 : ℝ) (103515367207/200000000000 : ℝ) (102311065383/200000000000 : ℝ) (255777663461/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4335/32768 : ℝ))) 2 (517576836029/1000000000000 : ℝ) (103515367207/200000000000 : ℝ) (102311065383/200000000000 : ℝ) (255777663461/500000000000 : ℝ) (8040095023/15625000000 : ℝ) (514566081479/1000000000000 : ℝ) (514557273351/1000000000000 : ℝ) (257278636679/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4335/32768 : ℝ))) 3 (8040095023/15625000000 : ℝ) (514566081479/1000000000000 : ℝ) (514557273351/1000000000000 : ℝ) (257278636679/500000000000 : ℝ) (514561677411/1000000000000 : ℝ) (514561677419/1000000000000 : ℝ) (32160104837/62500000000 : ℝ) (2572808387/5000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4335/32768 : ℝ))) 4 (514561677411/1000000000000 : ℝ) (514561677419/1000000000000 : ℝ) (32160104837/62500000000 : ℝ) (2572808387/5000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4335/32768 : ℝ))) 5 (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4335/32768 : ℝ))) 6 (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4335/32768 : ℝ))) 7 (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4335/32768 : ℝ)) hmem 8 (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4335/32768 : ℝ))) hcmem 8 (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4335/32768 : ℝ)) (4953085351/5000000000 : ℝ) (990617070203/1000000000000 : ℝ) (514561677401/1000000000000 : ℝ) (51456167741/100000000000 : ℝ) (203981845529/250000000000 : ℝ) (407963691067/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0119_exp_lower
  have heNumeric : (2019056175921/1000000000000 : ℝ)/4 ≤ Real.exp (-2734656794161/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019056175921/1000000000000 : ℝ)/4 ≤ Real.exp ((2167/16384 : ℝ)-(407963691067/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2167/16384 : ℝ) (4335/32768 : ℝ) (407963691067/500000000000 : ℝ) (2019056175921/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0120; no trusted numerical premise.
theorem cover7_leaf0120_exp_radius : (199527971409936191/200000000000000000 : ℝ) ≤ Real.exp ((-271/14336 : ℝ)/8) ∧ Real.exp ((-271/14336 : ℝ)/8) ≤ (249409964262420239/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-271/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0120_exp_lower : (918091610468274031/1000000000000000000 : ℝ) ≤ Real.exp ((-1093863677469/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093863677469/1600000000000 : ℝ)/8) ≤ (57380725654267127/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093863677469/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0120_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009527482367/500000000000 : ℝ) ≤ 4*Real.exp (4335/32768 : ℝ)*Real.exp (-mu (radius 7 (271/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (1009527482367/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (271/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0120_exp_radius
  have hrNumeric : (490637045023/500000000000 : ℝ) ≤ Real.exp (-271/14336 : ℝ) ∧ Real.exp (-271/14336 : ℝ) ≤ (981274090047/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490637045023/500000000000 : ℝ) ≤ (radius 7 (271/2048 : ℝ)) ∧ (radius 7 (271/2048 : ℝ)) ≤ (981274090047/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (271/2048 : ℝ)) (490637045023/500000000000 : ℝ) (981274090047/1000000000000 : ℝ) (96308307277/500000000000 : ℝ) (1203853841/6250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (271/2048 : ℝ)) (490637045023/500000000000 : ℝ) (981274090047/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (271/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490637045023/500000000000 : ℝ) (981274090047/1000000000000 : ℝ) (990637045023/1000000000000 : ℝ) (30957407657/31250000000 : ℝ) (990592797291/1000000000000 : ℝ) (990592797293/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (271/2048 : ℝ)) 1 (990637045023/1000000000000 : ℝ) (30957407657/31250000000 : ℝ) (990592797291/1000000000000 : ℝ) (990592797293/1000000000000 : ℝ) (990614921157/1000000000000 : ℝ) (990614921159/1000000000000 : ℝ) (990614920909/1000000000000 : ℝ) (61913432557/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (271/2048 : ℝ)) 2 (990614921157/1000000000000 : ℝ) (990614921159/1000000000000 : ℝ) (990614920909/1000000000000 : ℝ) (61913432557/62500000000 : ℝ) (990614921033/1000000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (271/2048 : ℝ)) 3 (990614921033/1000000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (271/2048 : ℝ)) 4 (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (271/2048 : ℝ)) 5 (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (271/2048 : ℝ)) 6 (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (271/2048 : ℝ)) 7 (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (271/2048 : ℝ))) (96308307277/500000000000 : ℝ) (1203853841/6250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (271/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96308307277/500000000000 : ℝ) (1203853841/6250000000 : ℝ) (596308307277/1000000000000 : ℝ) (7453853841/12500000000 : ℝ) (438881093867/1000000000000 : ℝ) (219440546937/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (271/2048 : ℝ))) 1 (596308307277/1000000000000 : ℝ) (7453853841/12500000000 : ℝ) (438881093867/1000000000000 : ℝ) (219440546937/500000000000 : ℝ) (129398675143/250000000000 : ℝ) (517594700577/1000000000000 : ℝ) (511574473737/1000000000000 : ℝ) (511574473743/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (271/2048 : ℝ))) 2 (129398675143/250000000000 : ℝ) (517594700577/1000000000000 : ℝ) (511574473737/1000000000000 : ℝ) (511574473743/1000000000000 : ℝ) (257292293577/500000000000 : ℝ) (12864614679/25000000000 : ℝ) (514575783101/1000000000000 : ℝ) (514575783107/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (271/2048 : ℝ))) 3 (257292293577/500000000000 : ℝ) (12864614679/25000000000 : ℝ) (514575783101/1000000000000 : ℝ) (514575783107/1000000000000 : ℝ) (514580185127/1000000000000 : ℝ) (257290092567/500000000000 : ℝ) (128645046277/250000000000 : ℝ) (102916037023/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (271/2048 : ℝ))) 4 (514580185127/1000000000000 : ℝ) (257290092567/500000000000 : ℝ) (128645046277/250000000000 : ℝ) (102916037023/200000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (271/2048 : ℝ))) 5 (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (271/2048 : ℝ))) 6 (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (271/2048 : ℝ))) 7 (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (271/2048 : ℝ)) hmem 8 (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (271/2048 : ℝ))) hcmem 8 (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (271/2048 : ℝ)) (123826865129/125000000000 : ℝ) (247653730259/250000000000 : ℝ) (514580185117/1000000000000 : ℝ) (4116641481/8000000000 : ℝ) (815958499573/1000000000000 : ℝ) (81595849959/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0120_exp_lower
  have heNumeric : (1009527482367/500000000000 : ℝ)/4 ≤ Real.exp (-1093863677469/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009527482367/500000000000 : ℝ)/4 ≤ Real.exp ((4335/32768 : ℝ)-(81595849959/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4335/32768 : ℝ) (271/2048 : ℝ) (81595849959/100000000000 : ℝ) (1009527482367/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0121; no trusted numerical premise.
theorem cover7_leaf0121_exp_radius : (498819656689626349/500000000000000000 : ℝ) ≤ Real.exp ((-4337/229376 : ℝ)/8) ∧ Real.exp ((-4337/229376 : ℝ)/8) ≤ (997639313379252699/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4337/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0121_exp_lower : (918091542175357903/1000000000000000000 : ℝ) ≤ Real.exp ((-21364543547/31250000000 : ℝ)/8) ∧ Real.exp ((-21364543547/31250000000 : ℝ)/8) ≤ (57380721385959869/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21364543547/31250000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0121_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019053763223/1000000000000 : ℝ) ≤ 4*Real.exp (271/2048 : ℝ)*Real.exp (-mu (radius 7 (4337/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019053763223/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4337/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0121_exp_radius
  have hrNumeric : (981269812039/1000000000000 : ℝ) ≤ Real.exp (-4337/229376 : ℝ) ∧ Real.exp (-4337/229376 : ℝ) ≤ (24531745301/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981269812039/1000000000000 : ℝ) ≤ (radius 7 (4337/32768 : ℝ)) ∧ (radius 7 (4337/32768 : ℝ)) ≤ (24531745301/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4337/32768 : ℝ)) (981269812039/1000000000000 : ℝ) (24531745301/25000000000 : ℝ) (19263840733/100000000000 : ℝ) (24079800917/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4337/32768 : ℝ)) (981269812039/1000000000000 : ℝ) (24531745301/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4337/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981269812039/1000000000000 : ℝ) (24531745301/25000000000 : ℝ) (990634906019/1000000000000 : ℝ) (49531745301/50000000000 : ℝ) (247647659493/250000000000 : ℝ) (495295318987/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4337/32768 : ℝ)) 1 (990634906019/1000000000000 : ℝ) (49531745301/50000000000 : ℝ) (247647659493/250000000000 : ℝ) (495295318987/500000000000 : ℝ) (198122554399/200000000000 : ℝ) (990612771997/1000000000000 : ℝ) (247653192937/250000000000 : ℝ) (3962451087/4000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4337/32768 : ℝ)) 2 (198122554399/200000000000 : ℝ) (990612771997/1000000000000 : ℝ) (247653192937/250000000000 : ℝ) (3962451087/4000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4337/32768 : ℝ)) 3 (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4337/32768 : ℝ)) 4 (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4337/32768 : ℝ)) 5 (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4337/32768 : ℝ)) 6 (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4337/32768 : ℝ)) 7 (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4337/32768 : ℝ))) (19263840733/100000000000 : ℝ) (24079800917/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4337/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19263840733/100000000000 : ℝ) (24079800917/125000000000 : ℝ) (119263840733/200000000000 : ℝ) (149079800917/250000000000 : ℝ) (438905920819/1000000000000 : ℝ) (219452960413/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4337/32768 : ℝ))) 1 (119263840733/200000000000 : ℝ) (149079800917/250000000000 : ℝ) (438905920819/1000000000000 : ℝ) (219452960413/500000000000 : ℝ) (258806281121/500000000000 : ℝ) (517612562247/1000000000000 : ℝ) (255796808613/500000000000 : ℝ) (31974601077/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4337/32768 : ℝ))) 2 (258806281121/500000000000 : ℝ) (517612562247/1000000000000 : ℝ) (255796808613/500000000000 : ℝ) (31974601077/62500000000 : ℝ) (257301544867/500000000000 : ℝ) (25730154487/50000000000 : ℝ) (102918857949/200000000000 : ℝ) (64324286219/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4337/32768 : ℝ))) 3 (257301544867/500000000000 : ℝ) (25730154487/50000000000 : ℝ) (102918857949/200000000000 : ℝ) (64324286219/125000000000 : ℝ) (514598689739/1000000000000 : ℝ) (257299344873/500000000000 : ℝ) (12864967243/25000000000 : ℝ) (8040604527/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4337/32768 : ℝ))) 4 (514598689739/1000000000000 : ℝ) (257299344873/500000000000 : ℝ) (12864967243/25000000000 : ℝ) (8040604527/15625000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4337/32768 : ℝ))) 5 (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4337/32768 : ℝ))) 6 (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4337/32768 : ℝ))) 7 (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4337/32768 : ℝ)) hmem 8 (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4337/32768 : ℝ))) hcmem 8 (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4337/32768 : ℝ)) (990612771871/1000000000000 : ℝ) (495306385937/500000000000 : ℝ) (514598689729/1000000000000 : ℝ) (514598689737/1000000000000 : ℝ) (407994806119/500000000000 : ℝ) (407994806127/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0121_exp_lower
  have heNumeric : (2019053763223/1000000000000 : ℝ)/4 ≤ Real.exp (-21364543547/31250000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019053763223/1000000000000 : ℝ)/4 ≤ Real.exp ((271/2048 : ℝ)-(407994806127/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (271/2048 : ℝ) (4337/32768 : ℝ) (407994806127/500000000000 : ℝ) (2019053763223/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0122; no trusted numerical premise.
theorem cover7_leaf0122_exp_radius : (498819384854560359/500000000000000000 : ℝ) ≤ Real.exp ((-2169/114688 : ℝ)/8) ∧ Real.exp ((-2169/114688 : ℝ)/8) ≤ (997638769709120719/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2169/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0122_exp_lower : (91809147443421983/100000000000000000 : ℝ) ≤ Real.exp ((-1093865574051/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093865574051/1600000000000 : ℝ)/8) ≤ (918091474434219831/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093865574051/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0122_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019052571421/1000000000000 : ℝ) ≤ 4*Real.exp (4337/32768 : ℝ)*Real.exp (-mu (radius 7 (2169/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019052571421/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2169/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0122_exp_radius
  have hrNumeric : (245316383513/250000000000 : ℝ) ≤ Real.exp (-2169/114688 : ℝ) ∧ Real.exp (-2169/114688 : ℝ) ≤ (981265534053/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245316383513/250000000000 : ℝ) ≤ (radius 7 (2169/16384 : ℝ)) ∧ (radius 7 (2169/16384 : ℝ)) ≤ (981265534053/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2169/16384 : ℝ)) (245316383513/250000000000 : ℝ) (981265534053/1000000000000 : ℝ) (38532039489/200000000000 : ℝ) (192660197451/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2169/16384 : ℝ)) (245316383513/250000000000 : ℝ) (981265534053/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2169/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245316383513/250000000000 : ℝ) (981265534053/1000000000000 : ℝ) (495316383513/500000000000 : ℝ) (990632767027/1000000000000 : ℝ) (990588478659/1000000000000 : ℝ) (49529423933/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2169/16384 : ℝ)) 1 (495316383513/500000000000 : ℝ) (990632767027/1000000000000 : ℝ) (990588478659/1000000000000 : ℝ) (49529423933/50000000000 : ℝ) (495305311421/500000000000 : ℝ) (247652655711/250000000000 : ℝ) (495305311297/500000000000 : ℝ) (247652655649/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2169/16384 : ℝ)) 2 (495305311421/500000000000 : ℝ) (247652655711/250000000000 : ℝ) (495305311297/500000000000 : ℝ) (247652655649/250000000000 : ℝ) (495305311359/500000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2169/16384 : ℝ)) 3 (495305311359/500000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2169/16384 : ℝ)) 4 (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2169/16384 : ℝ)) 5 (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2169/16384 : ℝ)) 6 (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2169/16384 : ℝ)) 7 (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2169/16384 : ℝ))) (38532039489/200000000000 : ℝ) (192660197451/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2169/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38532039489/200000000000 : ℝ) (192660197451/1000000000000 : ℝ) (298165049361/500000000000 : ℝ) (298165049363/500000000000 : ℝ) (87786148667/200000000000 : ℝ) (438930743343/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2169/16384 : ℝ))) 1 (298165049361/500000000000 : ℝ) (298165049363/500000000000 : ℝ) (87786148667/200000000000 : ℝ) (438930743343/1000000000000 : ℝ) (129407605257/250000000000 : ℝ) (103526084207/200000000000 : ℝ) (511612757371/1000000000000 : ℝ) (255806378689/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2169/16384 : ℝ))) 2 (129407605257/250000000000 : ℝ) (103526084207/200000000000 : ℝ) (511612757371/1000000000000 : ℝ) (255806378689/500000000000 : ℝ) (514621589199/1000000000000 : ℝ) (514621589207/1000000000000 : ℝ) (514612793273/1000000000000 : ℝ) (514612793281/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2169/16384 : ℝ))) 3 (514621589199/1000000000000 : ℝ) (514621589207/1000000000000 : ℝ) (514612793273/1000000000000 : ℝ) (514612793281/1000000000000 : ℝ) (128654297809/250000000000 : ℝ) (128654297811/250000000000 : ℝ) (514617191217/1000000000000 : ℝ) (257308595613/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2169/16384 : ℝ))) 4 (128654297809/250000000000 : ℝ) (128654297811/250000000000 : ℝ) (514617191217/1000000000000 : ℝ) (257308595613/500000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2169/16384 : ℝ))) 5 (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2169/16384 : ℝ))) 6 (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2169/16384 : ℝ))) 7 (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2169/16384 : ℝ)) hmem 8 (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2169/16384 : ℝ))) hcmem 8 (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2169/16384 : ℝ)) (990610622717/1000000000000 : ℝ) (773914549/781250000 : ℝ) (257308595613/500000000000 : ℝ) (102923438247/200000000000 : ℝ) (204005180023/250000000000 : ℝ) (81602072011/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0122_exp_lower
  have heNumeric : (2019052571421/1000000000000 : ℝ)/4 ≤ Real.exp (-1093865574051/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019052571421/1000000000000 : ℝ)/4 ≤ Real.exp ((4337/32768 : ℝ)-(81602072011/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4337/32768 : ℝ) (2169/16384 : ℝ) (81602072011/100000000000 : ℝ) (2019052571421/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0123; no trusted numerical premise.
theorem cover7_leaf0123_exp_radius : (199527645207857003/200000000000000000 : ℝ) ≤ Real.exp ((-4339/229376 : ℝ)/8) ∧ Real.exp ((-4339/229376 : ℝ)/8) ≤ (124704778254910627/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4339/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0123_exp_lower : (918091407243367793/1000000000000000000 : ℝ) ≤ Real.exp ((-2734666277059/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734666277059/4000000000000 : ℝ)/8) ≤ (459045703621683897/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734666277059/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0123_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (20190513893/10000000000 : ℝ) ≤ 4*Real.exp (2169/16384 : ℝ)*Real.exp (-mu (radius 7 (4339/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (20190513893/10000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4339/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0123_exp_radius
  have hrNumeric : (981261256083/1000000000000 : ℝ) ≤ Real.exp (-4339/229376 : ℝ) ∧ Real.exp (-4339/229376 : ℝ) ≤ (245315314021/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981261256083/1000000000000 : ℝ) ≤ (radius 7 (4339/32768 : ℝ)) ∧ (radius 7 (4339/32768 : ℝ)) ≤ (245315314021/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4339/32768 : ℝ)) (981261256083/1000000000000 : ℝ) (245315314021/250000000000 : ℝ) (48170496227/250000000000 : ℝ) (38536396983/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4339/32768 : ℝ)) (981261256083/1000000000000 : ℝ) (245315314021/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4339/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981261256083/1000000000000 : ℝ) (245315314021/250000000000 : ℝ) (990630628041/1000000000000 : ℝ) (495315314021/500000000000 : ℝ) (990586319349/1000000000000 : ℝ) (990586319351/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4339/32768 : ℝ)) 1 (990630628041/1000000000000 : ℝ) (495315314021/500000000000 : ℝ) (990586319349/1000000000000 : ℝ) (990586319351/1000000000000 : ℝ) (198121694739/200000000000 : ℝ) (990608473697/1000000000000 : ℝ) (990608473447/1000000000000 : ℝ) (990608473449/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4339/32768 : ℝ)) 2 (198121694739/200000000000 : ℝ) (990608473697/1000000000000 : ℝ) (990608473447/1000000000000 : ℝ) (990608473449/1000000000000 : ℝ) (990608473571/1000000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4339/32768 : ℝ)) 3 (990608473571/1000000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4339/32768 : ℝ)) 4 (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4339/32768 : ℝ)) 5 (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4339/32768 : ℝ)) 6 (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4339/32768 : ℝ)) 7 (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4339/32768 : ℝ))) (48170496227/250000000000 : ℝ) (38536396983/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4339/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48170496227/250000000000 : ℝ) (38536396983/200000000000 : ℝ) (298170496227/500000000000 : ℝ) (298170496229/500000000000 : ℝ) (438955561427/1000000000000 : ℝ) (109738890359/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4339/32768 : ℝ))) 1 (298170496227/500000000000 : ℝ) (298170496229/500000000000 : ℝ) (438955561427/1000000000000 : ℝ) (109738890359/250000000000 : ℝ) (25882413847/50000000000 : ℝ) (517648276947/1000000000000 : ℝ) (255815947091/500000000000 : ℝ) (51163189419/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4339/32768 : ℝ))) 2 (25882413847/50000000000 : ℝ) (517648276947/1000000000000 : ℝ) (255815947091/500000000000 : ℝ) (51163189419/100000000000 : ℝ) (514640085561/1000000000000 : ℝ) (514640085569/1000000000000 : ℝ) (102926258739/200000000000 : ℝ) (64328911713/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4339/32768 : ℝ))) 3 (514640085561/1000000000000 : ℝ) (514640085569/1000000000000 : ℝ) (102926258739/200000000000 : ℝ) (64328911713/125000000000 : ℝ) (128658922407/250000000000 : ℝ) (514635689637/1000000000000 : ℝ) (514635689609/1000000000000 : ℝ) (257317844809/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4339/32768 : ℝ))) 4 (128658922407/250000000000 : ℝ) (514635689637/1000000000000 : ℝ) (514635689609/1000000000000 : ℝ) (257317844809/500000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4339/32768 : ℝ))) 5 (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4339/32768 : ℝ))) 6 (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4339/32768 : ℝ))) 7 (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4339/32768 : ℝ)) hmem 8 (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4339/32768 : ℝ))) hcmem 8 (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4339/32768 : ℝ)) (99060847357/100000000000 : ℝ) (990608473573/1000000000000 : ℝ) (257317844809/500000000000 : ℝ) (128658922407/250000000000 : ℝ) (51003238947/62500000000 : ℝ) (816051823171/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0123_exp_lower
  have heNumeric : (20190513893/10000000000 : ℝ)/4 ≤ Real.exp (-2734666277059/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (20190513893/10000000000 : ℝ)/4 ≤ Real.exp ((2169/16384 : ℝ)-(816051823171/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2169/16384 : ℝ) (4339/32768 : ℝ) (816051823171/1000000000000 : ℝ) (20190513893/10000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0124; no trusted numerical premise.
theorem cover7_leaf0124_exp_radius : (249409420592436397/250000000000000000 : ℝ) ≤ Real.exp ((-155/8192 : ℝ)/8) ∧ Real.exp ((-155/8192 : ℝ)/8) ≤ (997637682369745589/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-155/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0124_exp_lower : (918091340603605001/1000000000000000000 : ℝ) ≤ Real.exp ((-1093867439913/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093867439913/1600000000000 : ℝ)/8) ≤ (459045670301802501/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093867439913/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0124_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504762554219/250000000000 : ℝ) ≤ 4*Real.exp (4339/32768 : ℝ)*Real.exp (-mu (radius 7 (1085/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504762554219/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1085/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0124_exp_radius
  have hrNumeric : (981256978133/1000000000000 : ℝ) ≤ Real.exp (-155/8192 : ℝ) ∧ Real.exp (-155/8192 : ℝ) ≤ (490628489067/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981256978133/1000000000000 : ℝ) ≤ (radius 7 (1085/8192 : ℝ)) ∧ (radius 7 (1085/8192 : ℝ)) ≤ (490628489067/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1085/8192 : ℝ)) (981256978133/1000000000000 : ℝ) (490628489067/500000000000 : ℝ) (192703769717/1000000000000 : ℝ) (192703769723/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1085/8192 : ℝ)) (981256978133/1000000000000 : ℝ) (490628489067/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1085/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981256978133/1000000000000 : ℝ) (490628489067/500000000000 : ℝ) (495314244533/500000000000 : ℝ) (990628489067/1000000000000 : ℝ) (198116832009/200000000000 : ℝ) (495292080023/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1085/8192 : ℝ)) 1 (495314244533/500000000000 : ℝ) (990628489067/1000000000000 : ℝ) (198116832009/200000000000 : ℝ) (495292080023/500000000000 : ℝ) (198121264911/200000000000 : ℝ) (990606324557/1000000000000 : ℝ) (990606324307/1000000000000 : ℝ) (990606324309/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1085/8192 : ℝ)) 2 (198121264911/200000000000 : ℝ) (990606324557/1000000000000 : ℝ) (990606324307/1000000000000 : ℝ) (990606324309/1000000000000 : ℝ) (990606324431/1000000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1085/8192 : ℝ)) 3 (990606324431/1000000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1085/8192 : ℝ)) 4 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1085/8192 : ℝ)) 5 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1085/8192 : ℝ)) 6 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1085/8192 : ℝ)) 7 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1085/8192 : ℝ))) (192703769717/1000000000000 : ℝ) (192703769723/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1085/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (192703769717/1000000000000 : ℝ) (192703769723/1000000000000 : ℝ) (298175942429/500000000000 : ℝ) (298175942431/500000000000 : ℝ) (438980375093/1000000000000 : ℝ) (438980375101/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1085/8192 : ℝ))) 1 (298175942429/500000000000 : ℝ) (298175942431/500000000000 : ℝ) (438980375093/1000000000000 : ℝ) (438980375101/1000000000000 : ℝ) (20706645199/40000000000 : ℝ) (258833064991/500000000000 : ℝ) (63956378457/125000000000 : ℝ) (31978189229/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1085/8192 : ℝ))) 2 (20706645199/40000000000 : ℝ) (258833064991/500000000000 : ℝ) (63956378457/125000000000 : ℝ) (31978189229/62500000000 : ℝ) (102931715763/200000000000 : ℝ) (514658578823/1000000000000 : ℝ) (514649791007/1000000000000 : ℝ) (64331223877/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1085/8192 : ℝ))) 3 (102931715763/200000000000 : ℝ) (514658578823/1000000000000 : ℝ) (514649791007/1000000000000 : ℝ) (64331223877/125000000000 : ℝ) (514654184911/1000000000000 : ℝ) (12866354623/25000000000 : ℝ) (128663546223/250000000000 : ℝ) (514654184901/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1085/8192 : ℝ))) 4 (514654184911/1000000000000 : ℝ) (12866354623/25000000000 : ℝ) (128663546223/250000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1085/8192 : ℝ))) 5 (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1085/8192 : ℝ))) 6 (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1085/8192 : ℝ))) 7 (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1085/8192 : ℝ)) hmem 8 (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1085/8192 : ℝ))) hcmem 8 (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1085/8192 : ℝ)) (99060632443/100000000000 : ℝ) (990606324433/1000000000000 : ℝ) (514654184901/1000000000000 : ℝ) (514654184911/1000000000000 : ℝ) (816082921411/1000000000000 : ℝ) (81608292143/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0124_exp_lower
  have heNumeric : (504762554219/250000000000 : ℝ)/4 ≤ Real.exp (-1093867439913/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504762554219/250000000000 : ℝ)/4 ≤ Real.exp ((4339/32768 : ℝ)-(81608292143/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4339/32768 : ℝ) (1085/8192 : ℝ) (81608292143/100000000000 : ℝ) (504762554219/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0100_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0100_certificate
#check SmaleRate.Proofs.cover7_leaf0101_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0101_certificate
#check SmaleRate.Proofs.cover7_leaf0102_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0102_certificate
#check SmaleRate.Proofs.cover7_leaf0103_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0103_certificate
#check SmaleRate.Proofs.cover7_leaf0104_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0104_certificate
#check SmaleRate.Proofs.cover7_leaf0105_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0105_certificate
#check SmaleRate.Proofs.cover7_leaf0106_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0106_certificate
#check SmaleRate.Proofs.cover7_leaf0107_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0107_certificate
#check SmaleRate.Proofs.cover7_leaf0108_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0108_certificate
#check SmaleRate.Proofs.cover7_leaf0109_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0109_certificate
#check SmaleRate.Proofs.cover7_leaf0110_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0110_certificate
#check SmaleRate.Proofs.cover7_leaf0111_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0111_certificate
#check SmaleRate.Proofs.cover7_leaf0112_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0112_certificate
#check SmaleRate.Proofs.cover7_leaf0113_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0113_certificate
#check SmaleRate.Proofs.cover7_leaf0114_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0114_certificate
#check SmaleRate.Proofs.cover7_leaf0115_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0115_certificate
#check SmaleRate.Proofs.cover7_leaf0116_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0116_certificate
#check SmaleRate.Proofs.cover7_leaf0117_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0117_certificate
#check SmaleRate.Proofs.cover7_leaf0118_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0118_certificate
#check SmaleRate.Proofs.cover7_leaf0119_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0119_certificate
#check SmaleRate.Proofs.cover7_leaf0120_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0120_certificate
#check SmaleRate.Proofs.cover7_leaf0121_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0121_certificate
#check SmaleRate.Proofs.cover7_leaf0122_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0122_certificate
#check SmaleRate.Proofs.cover7_leaf0123_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0123_certificate
#check SmaleRate.Proofs.cover7_leaf0124_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0124_certificate
