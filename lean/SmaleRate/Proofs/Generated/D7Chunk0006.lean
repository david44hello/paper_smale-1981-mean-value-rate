/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0150; no trusted numerical premise.
theorem cover7_leaf0150_exp_radius : (498811773532856501/500000000000000000 : ℝ) ≤ Real.exp ((-2183/114688 : ℝ)/8) ∧ Real.exp ((-2183/114688 : ℝ)/8) ≤ (997623547065713003/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2183/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0150_exp_lower : (918089800482142683/1000000000000000000 : ℝ) ≤ Real.exp ((-218777782451/320000000000 : ℝ)/8) ∧ Real.exp ((-218777782451/320000000000 : ℝ)/8) ≤ (229522450120535671/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-218777782451/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0150_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504755780243/250000000000 : ℝ) ≤ 4*Real.exp (4365/32768 : ℝ)*Real.exp (-mu (radius 7 (2183/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (504755780243/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2183/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0150_exp_radius
  have hrNumeric : (245286439493/250000000000 : ℝ) ≤ Real.exp (-2183/114688 : ℝ) ∧ Real.exp (-2183/114688 : ℝ) ≤ (981145757973/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245286439493/250000000000 : ℝ) ≤ (radius 7 (2183/16384 : ℝ)) ∧ (radius 7 (2183/16384 : ℝ)) ≤ (981145757973/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2183/16384 : ℝ)) (245286439493/250000000000 : ℝ) (981145757973/1000000000000 : ℝ) (193269246419/1000000000000 : ℝ) (7730769857/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2183/16384 : ℝ)) (245286439493/250000000000 : ℝ) (981145757973/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2183/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245286439493/250000000000 : ℝ) (981145757973/1000000000000 : ℝ) (495286439493/500000000000 : ℝ) (990572878987/1000000000000 : ℝ) (990528019781/1000000000000 : ℝ) (495264009891/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2183/16384 : ℝ)) 1 (495286439493/500000000000 : ℝ) (990572878987/1000000000000 : ℝ) (990528019781/1000000000000 : ℝ) (495264009891/500000000000 : ℝ) (990550449383/1000000000000 : ℝ) (198110089877/200000000000 : ℝ) (990550449129/1000000000000 : ℝ) (990550449131/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2183/16384 : ℝ)) 2 (990550449383/1000000000000 : ℝ) (198110089877/200000000000 : ℝ) (990550449129/1000000000000 : ℝ) (990550449131/1000000000000 : ℝ) (123818806157/125000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2183/16384 : ℝ)) 3 (123818806157/125000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2183/16384 : ℝ)) 4 (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2183/16384 : ℝ)) 5 (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2183/16384 : ℝ)) 6 (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2183/16384 : ℝ)) 7 (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2183/16384 : ℝ))) (193269246419/1000000000000 : ℝ) (7730769857/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2183/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193269246419/1000000000000 : ℝ) (7730769857/40000000000 : ℝ) (596634623209/1000000000000 : ℝ) (596634623213/1000000000000 : ℝ) (109905995747/250000000000 : ℝ) (109905995749/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2183/16384 : ℝ))) 1 (596634623209/1000000000000 : ℝ) (596634623213/1000000000000 : ℝ) (109905995747/250000000000 : ℝ) (109905995749/250000000000 : ℝ) (259064651549/500000000000 : ℝ) (103625860621/200000000000 : ℝ) (256073665887/500000000000 : ℝ) (512147331781/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2183/16384 : ℝ))) 2 (259064651549/500000000000 : ℝ) (103625860621/200000000000 : ℝ) (256073665887/500000000000 : ℝ) (512147331781/1000000000000 : ℝ) (128784579359/250000000000 : ℝ) (515138317443/1000000000000 : ℝ) (257564817131/500000000000 : ℝ) (51512963427/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2183/16384 : ℝ))) 3 (128784579359/250000000000 : ℝ) (515138317443/1000000000000 : ℝ) (257564817131/500000000000 : ℝ) (51512963427/100000000000 : ℝ) (515133975849/1000000000000 : ℝ) (515133975857/1000000000000 : ℝ) (51513397583/100000000000 : ℝ) (515133975839/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2183/16384 : ℝ))) 4 (515133975849/1000000000000 : ℝ) (515133975857/1000000000000 : ℝ) (51513397583/100000000000 : ℝ) (515133975839/1000000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2183/16384 : ℝ))) 5 (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2183/16384 : ℝ))) 6 (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2183/16384 : ℝ))) 7 (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2183/16384 : ℝ)) hmem 8 (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2183/16384 : ℝ))) hcmem 8 (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2183/16384 : ℝ)) (198110089851/200000000000 : ℝ) (495275224629/500000000000 : ℝ) (515133975839/1000000000000 : ℝ) (64391746981/125000000000 : ℝ) (408444899329/500000000000 : ℝ) (32675591947/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0150_exp_lower
  have heNumeric : (504755780243/250000000000 : ℝ)/4 ≤ Real.exp (-218777782451/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504755780243/250000000000 : ℝ)/4 ≤ Real.exp ((4365/32768 : ℝ)-(32675591947/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4365/32768 : ℝ) (2183/16384 : ℝ) (32675591947/40000000000 : ℝ) (504755780243/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0151; no trusted numerical premise.
theorem cover7_leaf0151_exp_radius : (997623003404172979/1000000000000000000 : ℝ) ≤ Real.exp ((-4367/229376 : ℝ)/8) ∧ Real.exp ((-4367/229376 : ℝ)/8) ≤ (49881150170208649/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4367/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0151_exp_lower : (229522437155849267/250000000000000000 : ℝ) ≤ Real.exp ((-2734724088173/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734724088173/4000000000000 : ℝ)/8) ≤ (918089748623397069/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734724088173/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0151_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019022208609/1000000000000 : ℝ) ≤ 4*Real.exp (2183/16384 : ℝ)*Real.exp (-mu (radius 7 (4367/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019022208609/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4367/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0151_exp_radius
  have hrNumeric : (39245659221/40000000000 : ℝ) ≤ Real.exp (-4367/229376 : ℝ) ∧ Real.exp (-4367/229376 : ℝ) ≤ (490570740263/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39245659221/40000000000 : ℝ) ≤ (radius 7 (4367/32768 : ℝ)) ∧ (radius 7 (4367/32768 : ℝ)) ≤ (490570740263/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4367/32768 : ℝ)) (39245659221/40000000000 : ℝ) (490570740263/500000000000 : ℝ) (193290959931/1000000000000 : ℝ) (193290959937/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4367/32768 : ℝ)) (39245659221/40000000000 : ℝ) (490570740263/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4367/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39245659221/40000000000 : ℝ) (490570740263/500000000000 : ℝ) (495285370131/500000000000 : ℝ) (990570740263/1000000000000 : ℝ) (990525860603/1000000000000 : ℝ) (198105172121/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4367/32768 : ℝ)) 1 (495285370131/500000000000 : ℝ) (990570740263/1000000000000 : ℝ) (990525860603/1000000000000 : ℝ) (198105172121/200000000000 : ℝ) (61909268777/62500000000 : ℝ) (495274150217/500000000000 : ℝ) (495274150089/500000000000 : ℝ) (49527415009/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4367/32768 : ℝ)) 2 (61909268777/62500000000 : ℝ) (495274150217/500000000000 : ℝ) (495274150089/500000000000 : ℝ) (49527415009/50000000000 : ℝ) (198109660061/200000000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4367/32768 : ℝ)) 3 (198109660061/200000000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4367/32768 : ℝ)) 4 (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4367/32768 : ℝ)) 5 (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4367/32768 : ℝ)) 6 (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4367/32768 : ℝ)) 7 (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4367/32768 : ℝ))) (193290959931/1000000000000 : ℝ) (193290959937/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4367/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193290959931/1000000000000 : ℝ) (193290959937/1000000000000 : ℝ) (119329095993/200000000000 : ℝ) (596645479969/1000000000000 : ℝ) (87929735569/200000000000 : ℝ) (109912169463/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4367/32768 : ℝ))) 1 (119329095993/200000000000 : ℝ) (596645479969/1000000000000 : ℝ) (87929735569/200000000000 : ℝ) (109912169463/250000000000 : ℝ) (103629415781/200000000000 : ℝ) (518147078911/1000000000000 : ℝ) (51216637571/100000000000 : ℝ) (512166375717/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4367/32768 : ℝ))) 2 (103629415781/200000000000 : ℝ) (518147078911/1000000000000 : ℝ) (51216637571/100000000000 : ℝ) (512166375717/1000000000000 : ℝ) (515156727307/1000000000000 : ℝ) (257578363657/500000000000 : ℝ) (824236877/1600000000 : ℝ) (128787012033/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4367/32768 : ℝ))) 3 (515156727307/1000000000000 : ℝ) (257578363657/500000000000 : ℝ) (824236877/1600000000 : ℝ) (128787012033/250000000000 : ℝ) (128788096929/250000000000 : ℝ) (515152387723/1000000000000 : ℝ) (515152387697/1000000000000 : ℝ) (103030477541/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4367/32768 : ℝ))) 4 (128788096929/250000000000 : ℝ) (515152387723/1000000000000 : ℝ) (515152387697/1000000000000 : ℝ) (103030477541/200000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4367/32768 : ℝ))) 5 (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4367/32768 : ℝ))) 6 (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4367/32768 : ℝ))) 7 (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4367/32768 : ℝ)) hmem 8 (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4367/32768 : ℝ))) hcmem 8 (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4367/32768 : ℝ)) (61909268769/62500000000 : ℝ) (990548300307/1000000000000 : ℝ) (257576193853/500000000000 : ℝ) (257576193857/500000000000 : ℝ) (816920768121/1000000000000 : ℝ) (816920768137/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0151_exp_lower
  have heNumeric : (2019022208609/1000000000000 : ℝ)/4 ≤ Real.exp (-2734724088173/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019022208609/1000000000000 : ℝ)/4 ≤ Real.exp ((2183/16384 : ℝ)-(816920768137/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2183/16384 : ℝ) (4367/32768 : ℝ) (816920768137/1000000000000 : ℝ) (2019022208609/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0152; no trusted numerical premise.
theorem cover7_leaf0152_exp_radius : (249405614935732307/250000000000000000 : ℝ) ≤ Real.exp ((-39/2048 : ℝ)/8) ∧ Real.exp ((-39/2048 : ℝ)/8) ≤ (997622459742929229/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-39/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0152_exp_lower : (229522424327270393/250000000000000000 : ℝ) ≤ Real.exp ((-1093890350693/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093890350693/1600000000000 : ℝ)/8) ≤ (918089697309081573/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093890350693/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0152_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (63094415807/31250000000 : ℝ) ≤ 4*Real.exp (4367/32768 : ℝ)*Real.exp (-mu (radius 7 (273/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (63094415807/31250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (273/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0152_exp_radius
  have hrNumeric : (981137203097/1000000000000 : ℝ) ≤ Real.exp (-39/2048 : ℝ) ∧ Real.exp (-39/2048 : ℝ) ≤ (490568601549/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981137203097/1000000000000 : ℝ) ≤ (radius 7 (273/2048 : ℝ)) ∧ (radius 7 (273/2048 : ℝ)) ≤ (490568601549/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (273/2048 : ℝ)) (981137203097/1000000000000 : ℝ) (490568601549/500000000000 : ℝ) (193312670813/1000000000000 : ℝ) (193312670819/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (273/2048 : ℝ)) (981137203097/1000000000000 : ℝ) (490568601549/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (273/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981137203097/1000000000000 : ℝ) (490568601549/500000000000 : ℝ) (247642150387/250000000000 : ℝ) (990568601549/1000000000000 : ℝ) (990523701431/1000000000000 : ℝ) (123815462679/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (273/2048 : ℝ)) 1 (247642150387/250000000000 : ℝ) (990568601549/1000000000000 : ℝ) (990523701431/1000000000000 : ℝ) (123815462679/125000000000 : ℝ) (990546151489/1000000000000 : ℝ) (990546151491/1000000000000 : ℝ) (198109230247/200000000000 : ℝ) (990546151237/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (273/2048 : ℝ)) 2 (990546151489/1000000000000 : ℝ) (990546151491/1000000000000 : ℝ) (198109230247/200000000000 : ℝ) (990546151237/1000000000000 : ℝ) (495273075681/500000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (273/2048 : ℝ)) 3 (495273075681/500000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (273/2048 : ℝ)) 4 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (273/2048 : ℝ)) 5 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (273/2048 : ℝ)) 6 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (273/2048 : ℝ)) 7 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (273/2048 : ℝ))) (193312670813/1000000000000 : ℝ) (193312670819/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (273/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193312670813/1000000000000 : ℝ) (193312670819/1000000000000 : ℝ) (298328167703/500000000000 : ℝ) (59665633541/100000000000 : ℝ) (439673368323/1000000000000 : ℝ) (439673368331/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (273/2048 : ℝ))) 1 (298328167703/500000000000 : ℝ) (59665633541/100000000000 : ℝ) (439673368323/1000000000000 : ℝ) (439673368331/1000000000000 : ℝ) (64770606483/125000000000 : ℝ) (518164851871/1000000000000 : ℝ) (512185416347/1000000000000 : ℝ) (102437083271/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (273/2048 : ℝ))) 2 (64770606483/125000000000 : ℝ) (518164851871/1000000000000 : ℝ) (512185416347/1000000000000 : ℝ) (102437083271/200000000000 : ℝ) (103035026821/200000000000 : ℝ) (515175134113/1000000000000 : ℝ) (16098951841/31250000000 : ℝ) (12879161473/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (273/2048 : ℝ))) 3 (103035026821/200000000000 : ℝ) (515175134113/1000000000000 : ℝ) (16098951841/31250000000 : ℝ) (12879161473/25000000000 : ℝ) (128792699127/250000000000 : ℝ) (515170796517/1000000000000 : ℝ) (51517079649/100000000000 : ℝ) (515170796499/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (273/2048 : ℝ))) 4 (128792699127/250000000000 : ℝ) (515170796517/1000000000000 : ℝ) (51517079649/100000000000 : ℝ) (515170796499/1000000000000 : ℝ) (515170796499/1000000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (273/2048 : ℝ))) 5 (515170796499/1000000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (273/2048 : ℝ))) 6 (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (273/2048 : ℝ))) 7 (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (273/2048 : ℝ)) hmem 8 (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (273/2048 : ℝ))) hcmem 8 (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (273/2048 : ℝ)) (990546151361/1000000000000 : ℝ) (247636537841/250000000000 : ℝ) (257585398249/500000000000 : ℝ) (128792699127/250000000000 : ℝ) (204237933209/250000000000 : ℝ) (163390346571/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0152_exp_lower
  have heNumeric : (63094415807/31250000000 : ℝ)/4 ≤ Real.exp (-1093890350693/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (63094415807/31250000000 : ℝ)/4 ≤ Real.exp ((4367/32768 : ℝ)-(163390346571/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4367/32768 : ℝ) (273/2048 : ℝ) (163390346571/200000000000 : ℝ) (63094415807/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0153; no trusted numerical premise.
theorem cover7_leaf0153_exp_radius : (249405479020495437/250000000000000000 : ℝ) ≤ Real.exp ((-4369/229376 : ℝ)/8) ∧ Real.exp ((-4369/229376 : ℝ)/8) ≤ (997621916081981749/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4369/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0153_exp_lower : (918089646539425627/1000000000000000000 : ℝ) ≤ Real.exp ((-683681911577/1000000000000 : ℝ)/8) ∧ Real.exp ((-683681911577/1000000000000 : ℝ)/8) ≤ (229522411634856407/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683681911577/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0153_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019020412621/1000000000000 : ℝ) ≤ 4*Real.exp (273/2048 : ℝ)*Real.exp (-mu (radius 7 (4369/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019020412621/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4369/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0153_exp_radius
  have hrNumeric : (122641615711/125000000000 : ℝ) ≤ Real.exp (-4369/229376 : ℝ) ∧ Real.exp (-4369/229376 : ℝ) ≤ (981132925689/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122641615711/125000000000 : ℝ) ≤ (radius 7 (4369/32768 : ℝ)) ∧ (radius 7 (4369/32768 : ℝ)) ≤ (981132925689/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4369/32768 : ℝ)) (122641615711/125000000000 : ℝ) (981132925689/1000000000000 : ℝ) (96667189533/500000000000 : ℝ) (3020849673/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4369/32768 : ℝ)) (122641615711/125000000000 : ℝ) (981132925689/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4369/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122641615711/125000000000 : ℝ) (981132925689/1000000000000 : ℝ) (247641615711/250000000000 : ℝ) (198113292569/200000000000 : ℝ) (990521542263/1000000000000 : ℝ) (123815192783/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4369/32768 : ℝ)) 1 (247641615711/250000000000 : ℝ) (198113292569/200000000000 : ℝ) (990521542263/1000000000000 : ℝ) (123815192783/125000000000 : ℝ) (990544002553/1000000000000 : ℝ) (198108800511/200000000000 : ℝ) (495272001149/500000000000 : ℝ) (9905440023/10000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4369/32768 : ℝ)) 2 (990544002553/1000000000000 : ℝ) (198108800511/200000000000 : ℝ) (495272001149/500000000000 : ℝ) (9905440023/10000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4369/32768 : ℝ)) 3 (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4369/32768 : ℝ)) 4 (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4369/32768 : ℝ)) 5 (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4369/32768 : ℝ)) 6 (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4369/32768 : ℝ)) 7 (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4369/32768 : ℝ))) (96667189533/500000000000 : ℝ) (3020849673/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4369/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96667189533/500000000000 : ℝ) (3020849673/15625000000 : ℝ) (596667189533/1000000000000 : ℝ) (18645849673/31250000000 : ℝ) (17587922177/40000000000 : ℝ) (439698054433/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4369/32768 : ℝ))) 1 (596667189533/1000000000000 : ℝ) (18645849673/31250000000 : ℝ) (17587922177/40000000000 : ℝ) (439698054433/1000000000000 : ℝ) (518182621979/1000000000000 : ℝ) (103636524397/200000000000 : ℝ) (512204453687/1000000000000 : ℝ) (256102226847/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4369/32768 : ℝ))) 2 (518182621979/1000000000000 : ℝ) (103636524397/200000000000 : ℝ) (512204453687/1000000000000 : ℝ) (256102226847/500000000000 : ℝ) (515193537833/1000000000000 : ℝ) (6439919223/12500000000 : ℝ) (257592433313/500000000000 : ℝ) (515184866633/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4369/32768 : ℝ))) 3 (515193537833/1000000000000 : ℝ) (6439919223/12500000000 : ℝ) (257592433313/500000000000 : ℝ) (515184866633/1000000000000 : ℝ) (515189202229/1000000000000 : ℝ) (515189202237/1000000000000 : ℝ) (515189202211/1000000000000 : ℝ) (515189202219/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4369/32768 : ℝ))) 4 (515189202229/1000000000000 : ℝ) (515189202237/1000000000000 : ℝ) (515189202211/1000000000000 : ℝ) (515189202219/1000000000000 : ℝ) (25759460111/50000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4369/32768 : ℝ))) 5 (25759460111/50000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4369/32768 : ℝ))) 6 (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4369/32768 : ℝ))) 7 (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4369/32768 : ℝ)) hmem 8 (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4369/32768 : ℝ))) hcmem 8 (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4369/32768 : ℝ)) (39621760097/40000000000 : ℝ) (247636000607/250000000000 : ℝ) (515189202219/1000000000000 : ℝ) (128797300557/250000000000 : ℝ) (816982692809/1000000000000 : ℝ) (816982692827/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0153_exp_lower
  have heNumeric : (2019020412621/1000000000000 : ℝ)/4 ≤ Real.exp (-683681911577/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019020412621/1000000000000 : ℝ)/4 ≤ Real.exp ((273/2048 : ℝ)-(816982692827/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (273/2048 : ℝ) (4369/32768 : ℝ) (816982692827/1000000000000 : ℝ) (2019020412621/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0154; no trusted numerical premise.
theorem cover7_leaf0154_exp_radius : (49881068621066527/50000000000000000 : ℝ) ≤ Real.exp ((-2185/114688 : ℝ)/8) ∧ Real.exp ((-2185/114688 : ℝ)/8) ≤ (997621372421330541/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2185/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0154_exp_lower : (229522399078349073/250000000000000000 : ℝ) ≤ Real.exp ((-5469458793871/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469458793871/8000000000000 : ℝ)/8) ≤ (918089596313396293/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469458793871/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0154_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019019528983/1000000000000 : ℝ) ≤ 4*Real.exp (4369/32768 : ℝ)*Real.exp (-mu (radius 7 (2185/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019019528983/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2185/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0154_exp_radius
  have hrNumeric : (981128648297/1000000000000 : ℝ) ≤ Real.exp (-2185/114688 : ℝ) ∧ Real.exp (-2185/114688 : ℝ) ≤ (490564324149/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981128648297/1000000000000 : ℝ) ≤ (radius 7 (2185/16384 : ℝ)) ∧ (radius 7 (2185/16384 : ℝ)) ≤ (490564324149/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2185/16384 : ℝ)) (981128648297/1000000000000 : ℝ) (490564324149/500000000000 : ℝ) (38671216939/200000000000 : ℝ) (96678042351/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2185/16384 : ℝ)) (981128648297/1000000000000 : ℝ) (490564324149/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2185/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981128648297/1000000000000 : ℝ) (490564324149/500000000000 : ℝ) (247641081037/250000000000 : ℝ) (990564324149/1000000000000 : ℝ) (9905193831/10000000000 : ℝ) (990519383101/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2185/16384 : ℝ)) 1 (247641081037/250000000000 : ℝ) (990564324149/1000000000000 : ℝ) (9905193831/10000000000 : ℝ) (990519383101/1000000000000 : ℝ) (123817731703/125000000000 : ℝ) (7924334829/8000000000 : ℝ) (990541853369/1000000000000 : ℝ) (990541853371/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2185/16384 : ℝ)) 2 (123817731703/125000000000 : ℝ) (7924334829/8000000000 : ℝ) (990541853369/1000000000000 : ℝ) (990541853371/1000000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2185/16384 : ℝ)) 3 (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2185/16384 : ℝ)) 4 (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2185/16384 : ℝ)) 5 (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2185/16384 : ℝ)) 6 (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2185/16384 : ℝ)) 7 (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2185/16384 : ℝ))) (38671216939/200000000000 : ℝ) (96678042351/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2185/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38671216939/200000000000 : ℝ) (96678042351/500000000000 : ℝ) (596678042347/1000000000000 : ℝ) (596678042351/1000000000000 : ℝ) (219861368079/500000000000 : ℝ) (439722736167/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2185/16384 : ℝ))) 1 (596678042347/1000000000000 : ℝ) (596678042351/1000000000000 : ℝ) (219861368079/500000000000 : ℝ) (439722736167/1000000000000 : ℝ) (129550097313/250000000000 : ℝ) (518200389259/1000000000000 : ℝ) (512223487733/1000000000000 : ℝ) (512223487741/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2185/16384 : ℝ))) 2 (129550097313/250000000000 : ℝ) (518200389259/1000000000000 : ℝ) (512223487733/1000000000000 : ℝ) (512223487741/1000000000000 : ℝ) (128802984623/250000000000 : ℝ) (1030423877/2000000000 : ℝ) (515203271269/1000000000000 : ℝ) (257601635639/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2185/16384 : ℝ))) 3 (128802984623/250000000000 : ℝ) (1030423877/2000000000 : ℝ) (515203271269/1000000000000 : ℝ) (257601635639/500000000000 : ℝ) (6440095061/12500000000 : ℝ) (515207604889/1000000000000 : ℝ) (257603802431/500000000000 : ℝ) (515207604871/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2185/16384 : ℝ))) 4 (6440095061/12500000000 : ℝ) (515207604889/1000000000000 : ℝ) (257603802431/500000000000 : ℝ) (515207604871/1000000000000 : ℝ) (515207604871/1000000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2185/16384 : ℝ))) 5 (515207604871/1000000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2185/16384 : ℝ))) 6 (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2185/16384 : ℝ))) 7 (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2185/16384 : ℝ)) hmem 8 (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2185/16384 : ℝ))) hcmem 8 (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2185/16384 : ℝ)) (123817731687/125000000000 : ℝ) (495270926749/500000000000 : ℝ) (51520760487/100000000000 : ℝ) (6440095061/12500000000 : ℝ) (817013648043/1000000000000 : ℝ) (408506824031/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0154_exp_lower
  have heNumeric : (2019019528983/1000000000000 : ℝ)/4 ≤ Real.exp (-5469458793871/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019019528983/1000000000000 : ℝ)/4 ≤ Real.exp ((4369/32768 : ℝ)-(408506824031/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4369/32768 : ℝ) (2185/16384 : ℝ) (408506824031/500000000000 : ℝ) (2019019528983/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0155; no trusted numerical premise.
theorem cover7_leaf0155_exp_radius : (249405207190243901/250000000000000000 : ℝ) ≤ Real.exp ((-4371/229376 : ℝ)/8) ∧ Real.exp ((-4371/229376 : ℝ)/8) ≤ (199524165752195121/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4371/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0155_exp_lower : (918089546630993477/1000000000000000000 : ℝ) ≤ Real.exp ((-546946225723/800000000000 : ℝ)/8) ∧ Real.exp ((-546946225723/800000000000 : ℝ)/8) ≤ (459044773315496739/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546946225723/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0155_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901865491/100000000000 : ℝ) ≤ 4*Real.exp (2185/16384 : ℝ)*Real.exp (-mu (radius 7 (4371/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (201901865491/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4371/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0155_exp_radius
  have hrNumeric : (39244974837/40000000000 : ℝ) ≤ Real.exp (-4371/229376 : ℝ) ∧ Real.exp (-4371/229376 : ℝ) ≤ (490562185463/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39244974837/40000000000 : ℝ) ≤ (radius 7 (4371/32768 : ℝ)) ∧ (radius 7 (4371/32768 : ℝ)) ≤ (490562185463/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4371/32768 : ℝ)) (39244974837/40000000000 : ℝ) (490562185463/500000000000 : ℝ) (96688893849/500000000000 : ℝ) (24172223463/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4371/32768 : ℝ)) (39244974837/40000000000 : ℝ) (490562185463/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4371/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39244974837/40000000000 : ℝ) (490562185463/500000000000 : ℝ) (495281092731/500000000000 : ℝ) (990562185463/1000000000000 : ℝ) (990517223941/1000000000000 : ℝ) (990517223943/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4371/32768 : ℝ)) 1 (495281092731/500000000000 : ℝ) (990562185463/1000000000000 : ℝ) (990517223941/1000000000000 : ℝ) (990517223943/1000000000000 : ℝ) (990539704701/1000000000000 : ℝ) (990539704703/1000000000000 : ℝ) (495269852223/500000000000 : ℝ) (7738591441/7812500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4371/32768 : ℝ)) 2 (990539704701/1000000000000 : ℝ) (990539704703/1000000000000 : ℝ) (495269852223/500000000000 : ℝ) (7738591441/7812500000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4371/32768 : ℝ)) 3 (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4371/32768 : ℝ)) 4 (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4371/32768 : ℝ)) 5 (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4371/32768 : ℝ)) 6 (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4371/32768 : ℝ)) 7 (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4371/32768 : ℝ))) (96688893849/500000000000 : ℝ) (24172223463/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4371/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96688893849/500000000000 : ℝ) (24172223463/125000000000 : ℝ) (596688893849/1000000000000 : ℝ) (149172223463/250000000000 : ℝ) (5496842669/12500000000 : ℝ) (54968426691/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4371/32768 : ℝ))) 1 (596688893849/1000000000000 : ℝ) (149172223463/250000000000 : ℝ) (5496842669/12500000000 : ℝ) (54968426691/125000000000 : ℝ) (129554538421/250000000000 : ℝ) (51821815369/100000000000 : ℝ) (512242518487/1000000000000 : ℝ) (256121259247/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4371/32768 : ℝ))) 2 (129554538421/250000000000 : ℝ) (51821815369/100000000000 : ℝ) (512242518487/1000000000000 : ℝ) (256121259247/500000000000 : ℝ) (103046067217/200000000000 : ℝ) (128807584023/250000000000 : ℝ) (128805418211/250000000000 : ℝ) (128805418213/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4371/32768 : ℝ))) 3 (103046067217/200000000000 : ℝ) (128807584023/250000000000 : ℝ) (128805418211/250000000000 : ℝ) (128805418213/250000000000 : ℝ) (32201625279/62500000000 : ℝ) (64403250559/125000000000 : ℝ) (257613002223/500000000000 : ℝ) (257613002227/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4371/32768 : ℝ))) 4 (32201625279/62500000000 : ℝ) (64403250559/125000000000 : ℝ) (257613002223/500000000000 : ℝ) (257613002227/500000000000 : ℝ) (103045200891/200000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4371/32768 : ℝ))) 5 (103045200891/200000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4371/32768 : ℝ))) 6 (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4371/32768 : ℝ))) 7 (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4371/32768 : ℝ)) hmem 8 (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4371/32768 : ℝ))) hcmem 8 (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4371/32768 : ℝ)) (990539704573/1000000000000 : ℝ) (3869295721/3906250000 : ℝ) (257613002227/500000000000 : ℝ) (515226004463/1000000000000 : ℝ) (408522299271/500000000000 : ℝ) (5106528741/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0155_exp_lower
  have heNumeric : (201901865491/100000000000 : ℝ)/4 ≤ Real.exp (-546946225723/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901865491/100000000000 : ℝ)/4 ≤ Real.exp ((2185/16384 : ℝ)-(5106528741/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2185/16384 : ℝ) (4371/32768 : ℝ) (5106528741/6250000000 : ℝ) (201901865491/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0156; no trusted numerical premise.
theorem cover7_leaf0156_exp_radius : (997620285100916939/1000000000000000000 : ℝ) ≤ Real.exp ((-1093/57344 : ℝ)/8) ∧ Real.exp ((-1093/57344 : ℝ)/8) ≤ (49881014255045847/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0156_exp_lower : (918089497492561377/1000000000000000000 : ℝ) ≤ Real.exp ((-5469465682669/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469465682669/8000000000000 : ℝ)/8) ≤ (459044748746280689/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469465682669/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0156_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019017790407/1000000000000 : ℝ) ≤ 4*Real.exp (4371/32768 : ℝ)*Real.exp (-mu (radius 7 (1093/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019017790407/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1093/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0156_exp_radius
  have hrNumeric : (245280023393/250000000000 : ℝ) ≤ Real.exp (-1093/57344 : ℝ) ∧ Real.exp (-1093/57344 : ℝ) ≤ (981120093573/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245280023393/250000000000 : ℝ) ≤ (radius 7 (1093/8192 : ℝ)) ∧ (radius 7 (1093/8192 : ℝ)) ≤ (981120093573/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1093/8192 : ℝ)) (245280023393/250000000000 : ℝ) (981120093573/1000000000000 : ℝ) (96699744037/500000000000 : ℝ) (2417493601/12500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1093/8192 : ℝ)) (245280023393/250000000000 : ℝ) (981120093573/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1093/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245280023393/250000000000 : ℝ) (981120093573/1000000000000 : ℝ) (495280023393/500000000000 : ℝ) (990560046787/1000000000000 : ℝ) (247628766197/250000000000 : ℝ) (990515064789/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1093/8192 : ℝ)) 1 (495280023393/500000000000 : ℝ) (990560046787/1000000000000 : ℝ) (247628766197/250000000000 : ℝ) (990515064789/1000000000000 : ℝ) (990537555787/1000000000000 : ℝ) (247634388947/250000000000 : ℝ) (990537555531/1000000000000 : ℝ) (990537555533/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1093/8192 : ℝ)) 2 (990537555787/1000000000000 : ℝ) (247634388947/250000000000 : ℝ) (990537555531/1000000000000 : ℝ) (990537555533/1000000000000 : ℝ) (990537555659/1000000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1093/8192 : ℝ)) 3 (990537555659/1000000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1093/8192 : ℝ)) 4 (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1093/8192 : ℝ)) 5 (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1093/8192 : ℝ)) 6 (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1093/8192 : ℝ)) 7 (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1093/8192 : ℝ))) (96699744037/500000000000 : ℝ) (2417493601/12500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1093/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96699744037/500000000000 : ℝ) (2417493601/12500000000 : ℝ) (596699744037/1000000000000 : ℝ) (14917493601/25000000000 : ℝ) (43977208651/100000000000 : ℝ) (219886043259/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1093/8192 : ℝ))) 1 (596699744037/1000000000000 : ℝ) (14917493601/25000000000 : ℝ) (43977208651/100000000000 : ℝ) (219886043259/500000000000 : ℝ) (518235915273/1000000000000 : ℝ) (518235915279/1000000000000 : ℝ) (256130772973/500000000000 : ℝ) (512261545953/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1093/8192 : ℝ))) 2 (518235915273/1000000000000 : ℝ) (518235915279/1000000000000 : ℝ) (256130772973/500000000000 : ℝ) (512261545953/1000000000000 : ℝ) (515248730609/1000000000000 : ℝ) (64406091327/125000000000 : ℝ) (515240071347/1000000000000 : ℝ) (103048014271/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1093/8192 : ℝ))) 3 (515248730609/1000000000000 : ℝ) (64406091327/125000000000 : ℝ) (515240071347/1000000000000 : ℝ) (103048014271/200000000000 : ℝ) (257622200489/500000000000 : ℝ) (257622200493/500000000000 : ℝ) (515244400959/1000000000000 : ℝ) (64405550121/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1093/8192 : ℝ))) 4 (257622200489/500000000000 : ℝ) (257622200493/500000000000 : ℝ) (515244400959/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1093/8192 : ℝ))) 5 (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1093/8192 : ℝ))) 6 (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1093/8192 : ℝ))) 7 (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1093/8192 : ℝ)) hmem 8 (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1093/8192 : ℝ))) hcmem 8 (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1093/8192 : ℝ)) (495268777829/500000000000 : ℝ) (990537555661/1000000000000 : ℝ) (64405550121/125000000000 : ℝ) (515244400977/1000000000000 : ℝ) (8170755443/10000000000 : ℝ) (408537772159/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0156_exp_lower
  have heNumeric : (2019017790407/1000000000000 : ℝ)/4 ≤ Real.exp (-5469465682669/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019017790407/1000000000000 : ℝ)/4 ≤ Real.exp ((4371/32768 : ℝ)-(408537772159/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4371/32768 : ℝ) (1093/8192 : ℝ) (408537772159/500000000000 : ℝ) (2019017790407/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0157; no trusted numerical premise.
theorem cover7_leaf0157_exp_radius : (199523948288230909/200000000000000000 : ℝ) ≤ Real.exp ((-4373/229376 : ℝ)/8) ∧ Real.exp ((-4373/229376 : ℝ)/8) ≤ (498809870720577273/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4373/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0157_exp_lower : (57380590556066691/62500000000000000 : ℝ) ≤ Real.exp ((-273473453513/400000000000 : ℝ)/8) ∧ Real.exp ((-273473453513/400000000000 : ℝ)/8) ≤ (918089448897067057/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273473453513/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0157_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (63094279233/31250000000 : ℝ) ≤ 4*Real.exp (1093/8192 : ℝ)*Real.exp (-mu (radius 7 (4373/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (63094279233/31250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4373/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0157_exp_radius
  have hrNumeric : (981115816237/1000000000000 : ℝ) ≤ Real.exp (-4373/229376 : ℝ) ∧ Real.exp (-4373/229376 : ℝ) ≤ (490557908119/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981115816237/1000000000000 : ℝ) ≤ (radius 7 (4373/32768 : ℝ)) ∧ (radius 7 (4373/32768 : ℝ)) ≤ (490557908119/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4373/32768 : ℝ)) (981115816237/1000000000000 : ℝ) (490557908119/500000000000 : ℝ) (193421185829/1000000000000 : ℝ) (38684237167/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4373/32768 : ℝ)) (981115816237/1000000000000 : ℝ) (490557908119/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4373/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981115816237/1000000000000 : ℝ) (490557908119/500000000000 : ℝ) (495278954059/500000000000 : ℝ) (990557908119/1000000000000 : ℝ) (495256452819/500000000000 : ℝ) (24762822641/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4373/32768 : ℝ)) 1 (495278954059/500000000000 : ℝ) (990557908119/1000000000000 : ℝ) (495256452819/500000000000 : ℝ) (24762822641/25000000000 : ℝ) (495267703439/500000000000 : ℝ) (6190846293/6250000000 : ℝ) (495267703311/500000000000 : ℝ) (30954231457/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4373/32768 : ℝ)) 2 (495267703439/500000000000 : ℝ) (6190846293/6250000000 : ℝ) (495267703311/500000000000 : ℝ) (30954231457/31250000000 : ℝ) (3962141627/4000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4373/32768 : ℝ)) 3 (3962141627/4000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4373/32768 : ℝ)) 4 (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4373/32768 : ℝ)) 5 (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4373/32768 : ℝ)) 6 (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4373/32768 : ℝ)) 7 (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4373/32768 : ℝ))) (193421185829/1000000000000 : ℝ) (38684237167/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4373/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193421185829/1000000000000 : ℝ) (38684237167/200000000000 : ℝ) (298355296457/500000000000 : ℝ) (298355296459/500000000000 : ℝ) (6871824299/15625000000 : ℝ) (54974594393/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4373/32768 : ℝ))) 1 (298355296457/500000000000 : ℝ) (298355296459/500000000000 : ℝ) (6871824299/15625000000 : ℝ) (54974594393/125000000000 : ℝ) (20730146961/40000000000 : ℝ) (518253674031/1000000000000 : ℝ) (128070142529/250000000000 : ℝ) (512280570123/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4373/32768 : ℝ))) 2 (20730146961/40000000000 : ℝ) (518253674031/1000000000000 : ℝ) (128070142529/250000000000 : ℝ) (512280570123/1000000000000 : ℝ) (51526712207/100000000000 : ℝ) (515267122077/1000000000000 : ℝ) (103051693357/200000000000 : ℝ) (515258466793/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4373/32768 : ℝ))) 3 (51526712207/100000000000 : ℝ) (515267122077/1000000000000 : ℝ) (103051693357/200000000000 : ℝ) (515258466793/1000000000000 : ℝ) (515262794427/1000000000000 : ℝ) (103052558887/200000000000 : ℝ) (515262794409/1000000000000 : ℝ) (515262794417/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4373/32768 : ℝ))) 4 (515262794427/1000000000000 : ℝ) (103052558887/200000000000 : ℝ) (515262794409/1000000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397209/500000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4373/32768 : ℝ))) 5 (257631397209/500000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4373/32768 : ℝ))) 6 (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4373/32768 : ℝ))) 7 (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4373/32768 : ℝ)) hmem 8 (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4373/32768 : ℝ))) hcmem 8 (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4373/32768 : ℝ)) (990535406749/1000000000000 : ℝ) (30954231461/31250000000 : ℝ) (515262794417/1000000000000 : ℝ) (257631397213/500000000000 : ℝ) (51069155333/62500000000 : ℝ) (163421297069/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0157_exp_lower
  have heNumeric : (63094279233/31250000000 : ℝ)/4 ≤ Real.exp (-273473453513/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (63094279233/31250000000 : ℝ)/4 ≤ Real.exp ((1093/8192 : ℝ)-(163421297069/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1093/8192 : ℝ) (4373/32768 : ℝ) (163421297069/200000000000 : ℝ) (63094279233/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0158; no trusted numerical premise.
theorem cover7_leaf0158_exp_radius : (498809598890844211/500000000000000000 : ℝ) ≤ Real.exp ((-2187/114688 : ℝ)/8) ∧ Real.exp ((-2187/114688 : ℝ)/8) ≤ (997619197781688423/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0158_exp_lower : (918089400844625187/1000000000000000000 : ℝ) ≤ Real.exp ((-1093894483999/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093894483999/1600000000000 : ℝ)/8) ≤ (229522350211156297/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093894483999/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0158_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (100950804503/50000000000 : ℝ) ≤ 4*Real.exp (4373/32768 : ℝ)*Real.exp (-mu (radius 7 (2187/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (100950804503/50000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2187/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0158_exp_radius
  have hrNumeric : (981111538921/1000000000000 : ℝ) ≤ Real.exp (-2187/114688 : ℝ) ∧ Real.exp (-2187/114688 : ℝ) ≤ (490555769461/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981111538921/1000000000000 : ℝ) ≤ (radius 7 (2187/16384 : ℝ)) ∧ (radius 7 (2187/16384 : ℝ)) ≤ (490555769461/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2187/16384 : ℝ)) (981111538921/1000000000000 : ℝ) (490555769461/500000000000 : ℝ) (604509003/3125000000 : ℝ) (96721440483/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2187/16384 : ℝ)) (981111538921/1000000000000 : ℝ) (490555769461/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2187/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981111538921/1000000000000 : ℝ) (490555769461/500000000000 : ℝ) (49527788473/50000000000 : ℝ) (990555769461/1000000000000 : ℝ) (495255373247/500000000000 : ℝ) (198102149299/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2187/16384 : ℝ)) 1 (49527788473/50000000000 : ℝ) (990555769461/1000000000000 : ℝ) (495255373247/500000000000 : ℝ) (198102149299/200000000000 : ℝ) (990533257977/1000000000000 : ℝ) (495266628989/500000000000 : ℝ) (990533257721/1000000000000 : ℝ) (990533257723/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2187/16384 : ℝ)) 2 (990533257977/1000000000000 : ℝ) (495266628989/500000000000 : ℝ) (990533257721/1000000000000 : ℝ) (990533257723/1000000000000 : ℝ) (990533257849/1000000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2187/16384 : ℝ)) 3 (990533257849/1000000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2187/16384 : ℝ)) 4 (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2187/16384 : ℝ)) 5 (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2187/16384 : ℝ)) 6 (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2187/16384 : ℝ)) 7 (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2187/16384 : ℝ))) (604509003/3125000000 : ℝ) (96721440483/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2187/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (604509003/3125000000 : ℝ) (96721440483/500000000000 : ℝ) (3729509003/6250000000 : ℝ) (596721440483/1000000000000 : ℝ) (109955354849/250000000000 : ℝ) (109955354851/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2187/16384 : ℝ))) 1 (3729509003/6250000000 : ℝ) (596721440483/1000000000000 : ℝ) (109955354849/250000000000 : ℝ) (109955354851/250000000000 : ℝ) (259135714969/500000000000 : ℝ) (64783928743/125000000000 : ℝ) (512299590997/1000000000000 : ℝ) (128074897751/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2187/16384 : ℝ))) 2 (259135714969/500000000000 : ℝ) (64783928743/125000000000 : ℝ) (512299590997/1000000000000 : ℝ) (128074897751/250000000000 : ℝ) (515285510467/1000000000000 : ℝ) (257642755237/500000000000 : ℝ) (128819214789/250000000000 : ℝ) (128819214791/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2187/16384 : ℝ))) 3 (515285510467/1000000000000 : ℝ) (257642755237/500000000000 : ℝ) (128819214789/250000000000 : ℝ) (128819214791/250000000000 : ℝ) (515281184811/1000000000000 : ℝ) (515281184819/1000000000000 : ℝ) (515281184793/1000000000000 : ℝ) (515281184801/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2187/16384 : ℝ))) 4 (515281184811/1000000000000 : ℝ) (515281184819/1000000000000 : ℝ) (515281184793/1000000000000 : ℝ) (515281184801/1000000000000 : ℝ) (257640592401/500000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2187/16384 : ℝ))) 5 (257640592401/500000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2187/16384 : ℝ))) 6 (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2187/16384 : ℝ))) 7 (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2187/16384 : ℝ)) hmem 8 (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2187/16384 : ℝ))) hcmem 8 (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2187/16384 : ℝ)) (123816657231/125000000000 : ℝ) (990533257851/1000000000000 : ℝ) (515281184801/1000000000000 : ℝ) (51528118481/100000000000 : ℝ) (408568710811/500000000000 : ℝ) (20428435541/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0158_exp_lower
  have heNumeric : (100950804503/50000000000 : ℝ)/4 ≤ Real.exp (-1093894483999/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (100950804503/50000000000 : ℝ)/4 ≤ Real.exp ((4373/32768 : ℝ)-(20428435541/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4373/32768 : ℝ) (2187/16384 : ℝ) (20428435541/25000000000 : ℝ) (100950804503/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0159; no trusted numerical premise.
theorem cover7_leaf0159_exp_radius : (99761865412251857/100000000000000000 : ℝ) ≤ Real.exp ((-625/32768 : ℝ)/8) ∧ Real.exp ((-625/32768 : ℝ)/8) ≤ (997618654122518571/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-625/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0159_exp_lower : (918089353334661879/1000000000000000000 : ℝ) ≤ Real.exp ((-2734737865957/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734737865957/4000000000000 : ℝ)/8) ≤ (22952233833366547/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734737865957/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0159_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (31547113347/15625000000 : ℝ) ≤ 4*Real.exp (2187/16384 : ℝ)*Real.exp (-mu (radius 7 (4375/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (31547113347/15625000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4375/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0159_exp_radius
  have hrNumeric : (981107261623/1000000000000 : ℝ) ≤ Real.exp (-625/32768 : ℝ) ∧ Real.exp (-625/32768 : ℝ) ≤ (122638407703/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981107261623/1000000000000 : ℝ) ≤ (radius 7 (4375/32768 : ℝ)) ∧ (radius 7 (4375/32768 : ℝ)) ≤ (122638407703/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4375/32768 : ℝ)) (981107261623/1000000000000 : ℝ) (122638407703/125000000000 : ℝ) (193464573471/1000000000000 : ℝ) (193464573477/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4375/32768 : ℝ)) (981107261623/1000000000000 : ℝ) (122638407703/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4375/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981107261623/1000000000000 : ℝ) (122638407703/125000000000 : ℝ) (990553630811/1000000000000 : ℝ) (247638407703/250000000000 : ℝ) (495254293677/500000000000 : ℝ) (247627146839/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4375/32768 : ℝ)) 1 (990553630811/1000000000000 : ℝ) (247638407703/250000000000 : ℝ) (495254293677/500000000000 : ℝ) (247627146839/250000000000 : ℝ) (495265554541/500000000000 : ℝ) (247632777271/250000000000 : ℝ) (495265554413/500000000000 : ℝ) (247632777207/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4375/32768 : ℝ)) 2 (495265554541/500000000000 : ℝ) (247632777271/250000000000 : ℝ) (495265554413/500000000000 : ℝ) (247632777207/250000000000 : ℝ) (495265554477/500000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4375/32768 : ℝ)) 3 (495265554477/500000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4375/32768 : ℝ)) 4 (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4375/32768 : ℝ)) 5 (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4375/32768 : ℝ)) 6 (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4375/32768 : ℝ)) 7 (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4375/32768 : ℝ))) (193464573471/1000000000000 : ℝ) (193464573477/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4375/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193464573471/1000000000000 : ℝ) (193464573477/1000000000000 : ℝ) (119346457347/200000000000 : ℝ) (596732286739/1000000000000 : ℝ) (219923039647/500000000000 : ℝ) (219923039651/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4375/32768 : ℝ))) 1 (119346457347/200000000000 : ℝ) (596732286739/1000000000000 : ℝ) (219923039647/500000000000 : ℝ) (219923039651/500000000000 : ℝ) (259144591507/500000000000 : ℝ) (518289183021/1000000000000 : ℝ) (51231860859/100000000000 : ℝ) (256159304299/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4375/32768 : ℝ))) 2 (259144591507/500000000000 : ℝ) (518289183021/1000000000000 : ℝ) (51231860859/100000000000 : ℝ) (256159304299/500000000000 : ℝ) (257651947901/500000000000 : ℝ) (51530389581/100000000000 : ℝ) (515295248463/1000000000000 : ℝ) (515295248471/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4375/32768 : ℝ))) 3 (257651947901/500000000000 : ℝ) (51530389581/100000000000 : ℝ) (515295248463/1000000000000 : ℝ) (515295248471/1000000000000 : ℝ) (128824893033/250000000000 : ℝ) (515299572141/1000000000000 : ℝ) (257649786057/500000000000 : ℝ) (515299572123/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4375/32768 : ℝ))) 4 (128824893033/250000000000 : ℝ) (515299572141/1000000000000 : ℝ) (257649786057/500000000000 : ℝ) (515299572123/1000000000000 : ℝ) (515299572123/1000000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4375/32768 : ℝ))) 5 (515299572123/1000000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4375/32768 : ℝ))) 6 (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4375/32768 : ℝ))) 7 (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4375/32768 : ℝ)) hmem 8 (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4375/32768 : ℝ))) hcmem 8 (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4375/32768 : ℝ)) (990531108953/1000000000000 : ℝ) (247632777239/250000000000 : ℝ) (257649786061/500000000000 : ℝ) (128824893033/250000000000 : ℝ) (817168353189/1000000000000 : ℝ) (102146044151/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0159_exp_lower
  have heNumeric : (31547113347/15625000000 : ℝ)/4 ≤ Real.exp (-2734737865957/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (31547113347/15625000000 : ℝ)/4 ≤ Real.exp ((2187/16384 : ℝ)-(102146044151/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2187/16384 : ℝ) (4375/32768 : ℝ) (102146044151/125000000000 : ℝ) (31547113347/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0160; no trusted numerical premise.
theorem cover7_leaf0160_exp_radius : (249404527615911247/250000000000000000 : ℝ) ≤ Real.exp ((-547/28672 : ℝ)/8) ∧ Real.exp ((-547/28672 : ℝ)/8) ≤ (997618110463644989/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-547/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0160_exp_lower : (57380581647991601/62500000000000000 : ℝ) ≤ Real.exp ((-5469479005969/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469479005969/8000000000000 : ℝ)/8) ≤ (918089306367865617/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469479005969/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0160_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376803489/125000000000 : ℝ) ≤ 4*Real.exp (4375/32768 : ℝ)*Real.exp (-mu (radius 7 (547/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (252376803489/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (547/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0160_exp_radius
  have hrNumeric : (122637873043/125000000000 : ℝ) ≤ Real.exp (-547/28672 : ℝ) ∧ Real.exp (-547/28672 : ℝ) ≤ (196220596869/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122637873043/125000000000 : ℝ) ≤ (radius 7 (547/4096 : ℝ)) ∧ (radius 7 (547/4096 : ℝ)) ≤ (196220596869/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (547/4096 : ℝ)) (122637873043/125000000000 : ℝ) (196220596869/200000000000 : ℝ) (604644573/3125000000 : ℝ) (96743131683/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (547/4096 : ℝ)) (122637873043/125000000000 : ℝ) (196220596869/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (547/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122637873043/125000000000 : ℝ) (196220596869/200000000000 : ℝ) (247637873043/250000000000 : ℝ) (990551492173/1000000000000 : ℝ) (990506428219/1000000000000 : ℝ) (49525321411/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (547/4096 : ℝ)) 1 (247637873043/250000000000 : ℝ) (990551492173/1000000000000 : ℝ) (990506428219/1000000000000 : ℝ) (49525321411/50000000000 : ℝ) (198105792039/200000000000 : ℝ) (990528960197/1000000000000 : ℝ) (990528959939/1000000000000 : ℝ) (990528959941/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (547/4096 : ℝ)) 2 (198105792039/200000000000 : ℝ) (990528960197/1000000000000 : ℝ) (990528959939/1000000000000 : ℝ) (990528959941/1000000000000 : ℝ) (990528960067/1000000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (547/4096 : ℝ)) 3 (990528960067/1000000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (547/4096 : ℝ)) 4 (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (547/4096 : ℝ)) 5 (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (547/4096 : ℝ)) 6 (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (547/4096 : ℝ)) 7 (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (547/4096 : ℝ))) (604644573/3125000000 : ℝ) (96743131683/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (547/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (604644573/3125000000 : ℝ) (96743131683/500000000000 : ℝ) (3729644573/6250000000 : ℝ) (596743131683/1000000000000 : ℝ) (43987073483/100000000000 : ℝ) (439870734837/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (547/4096 : ℝ))) 1 (3729644573/6250000000 : ℝ) (596743131683/1000000000000 : ℝ) (43987073483/100000000000 : ℝ) (439870734837/1000000000000 : ℝ) (103661386651/200000000000 : ℝ) (25915346663/50000000000 : ℝ) (256168811449/500000000000 : ℝ) (64042202863/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (547/4096 : ℝ))) 2 (103661386651/200000000000 : ℝ) (25915346663/50000000000 : ℝ) (256168811449/500000000000 : ℝ) (64042202863/125000000000 : ℝ) (128830569519/250000000000 : ℝ) (257661139041/500000000000 : ℝ) (515313634707/1000000000000 : ℝ) (515313634713/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (547/4096 : ℝ))) 3 (128830569519/250000000000 : ℝ) (257661139041/500000000000 : ℝ) (515313634707/1000000000000 : ℝ) (515313634713/1000000000000 : ℝ) (515317956391/1000000000000 : ℝ) (257658978199/500000000000 : ℝ) (515317956373/1000000000000 : ℝ) (25765897819/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (547/4096 : ℝ))) 4 (515317956391/1000000000000 : ℝ) (257658978199/500000000000 : ℝ) (515317956373/1000000000000 : ℝ) (25765897819/50000000000 : ℝ) (257658978191/500000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (547/4096 : ℝ))) 5 (257658978191/500000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (547/4096 : ℝ))) 6 (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (547/4096 : ℝ))) 7 (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (547/4096 : ℝ)) hmem 8 (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (547/4096 : ℝ))) hcmem 8 (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (547/4096 : ℝ)) (495264480033/500000000000 : ℝ) (990528960069/1000000000000 : ℝ) (515317956381/1000000000000 : ℝ) (515317956389/1000000000000 : ℝ) (817199280027/1000000000000 : ℝ) (817199280043/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0160_exp_lower
  have heNumeric : (252376803489/125000000000 : ℝ)/4 ≤ Real.exp (-5469479005969/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376803489/125000000000 : ℝ)/4 ≤ Real.exp ((4375/32768 : ℝ)-(817199280043/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4375/32768 : ℝ) (547/4096 : ℝ) (817199280043/1000000000000 : ℝ) (252376803489/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0161; no trusted numerical premise.
theorem cover7_leaf0161_exp_radius : (997617566805067677/1000000000000000000 : ℝ) ≤ Real.exp ((-4377/229376 : ℝ)/8) ∧ Real.exp ((-4377/229376 : ℝ)/8) ≤ (498808783402533839/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4377/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0161_exp_lower : (183617851988686597/200000000000000000 : ℝ) ≤ Real.exp ((-683685280277/1000000000000 : ℝ)/8) ∧ Real.exp ((-683685280277/1000000000000 : ℝ)/8) ≤ (459044629971716493/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683685280277/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0161_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506805579/500000000000 : ℝ) ≤ 4*Real.exp (547/4096 : ℝ)*Real.exp (-mu (radius 7 (4377/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506805579/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4377/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0161_exp_radius
  have hrNumeric : (245274676771/250000000000 : ℝ) ≤ Real.exp (-4377/229376 : ℝ) ∧ Real.exp (-4377/229376 : ℝ) ≤ (196219741417/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245274676771/250000000000 : ℝ) ≤ (radius 7 (4377/32768 : ℝ)) ∧ (radius 7 (4377/32768 : ℝ)) ≤ (196219741417/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4377/32768 : ℝ)) (245274676771/250000000000 : ℝ) (196219741417/200000000000 : ℝ) (193507950627/1000000000000 : ℝ) (193507950633/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4377/32768 : ℝ)) (245274676771/250000000000 : ℝ) (196219741417/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4377/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245274676771/250000000000 : ℝ) (196219741417/200000000000 : ℝ) (495274676771/500000000000 : ℝ) (990549353543/1000000000000 : ℝ) (990504269089/1000000000000 : ℝ) (99050426909/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4377/32768 : ℝ)) 1 (495274676771/500000000000 : ℝ) (990549353543/1000000000000 : ℝ) (990504269089/1000000000000 : ℝ) (99050426909/100000000000 : ℝ) (198105362263/200000000000 : ℝ) (990526811317/1000000000000 : ℝ) (495263405529/500000000000 : ℝ) (49526340553/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4377/32768 : ℝ)) 2 (198105362263/200000000000 : ℝ) (990526811317/1000000000000 : ℝ) (495263405529/500000000000 : ℝ) (49526340553/50000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4377/32768 : ℝ)) 3 (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4377/32768 : ℝ)) 4 (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4377/32768 : ℝ)) 5 (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4377/32768 : ℝ)) 6 (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4377/32768 : ℝ)) 7 (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4377/32768 : ℝ))) (193507950627/1000000000000 : ℝ) (193507950633/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4377/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193507950627/1000000000000 : ℝ) (193507950633/1000000000000 : ℝ) (596753975313/1000000000000 : ℝ) (596753975317/1000000000000 : ℝ) (439895386003/1000000000000 : ℝ) (439895386011/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4377/32768 : ℝ))) 1 (596753975313/1000000000000 : ℝ) (596753975317/1000000000000 : ℝ) (439895386003/1000000000000 : ℝ) (439895386011/1000000000000 : ℝ) (259162340329/500000000000 : ℝ) (64790585083/125000000000 : ℝ) (512356633917/1000000000000 : ℝ) (128089158481/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4377/32768 : ℝ))) 2 (259162340329/500000000000 : ℝ) (64790585083/125000000000 : ℝ) (512356633917/1000000000000 : ℝ) (128089158481/250000000000 : ℝ) (515340657287/1000000000000 : ℝ) (257670328647/500000000000 : ℝ) (103066403577/200000000000 : ℝ) (515332017893/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4377/32768 : ℝ))) 3 (515340657287/1000000000000 : ℝ) (257670328647/500000000000 : ℝ) (103066403577/200000000000 : ℝ) (515332017893/1000000000000 : ℝ) (257668168793/500000000000 : ℝ) (257668168797/500000000000 : ℝ) (515336337567/1000000000000 : ℝ) (64417042197/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4377/32768 : ℝ))) 4 (257668168793/500000000000 : ℝ) (257668168797/500000000000 : ℝ) (515336337567/1000000000000 : ℝ) (64417042197/125000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4377/32768 : ℝ))) 5 (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4377/32768 : ℝ))) 6 (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4377/32768 : ℝ))) 7 (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4377/32768 : ℝ)) hmem 8 (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4377/32768 : ℝ))) hcmem 8 (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4377/32768 : ℝ)) (495263405593/500000000000 : ℝ) (990526811189/1000000000000 : ℝ) (64417042197/125000000000 : ℝ) (103067267517/200000000000 : ℝ) (163446040427/200000000000 : ℝ) (102153775269/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0161_exp_lower
  have heNumeric : (1009506805579/500000000000 : ℝ)/4 ≤ Real.exp (-683685280277/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506805579/500000000000 : ℝ)/4 ≤ Real.exp ((547/4096 : ℝ)-(102153775269/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (547/4096 : ℝ) (4377/32768 : ℝ) (102153775269/125000000000 : ℝ) (1009506805579/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0162; no trusted numerical premise.
theorem cover7_leaf0162_exp_radius : (997617023146786637/1000000000000000000 : ℝ) ≤ Real.exp ((-2189/114688 : ℝ)/8) ∧ Real.exp ((-2189/114688 : ℝ)/8) ≤ (498808511573393319/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2189/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0162_exp_lower : (918089214060904861/1000000000000000000 : ℝ) ≤ Real.exp ((-5469485440687/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469485440687/8000000000000 : ℝ)/8) ≤ (459044607030452431/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469485440687/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0162_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019012803939/1000000000000 : ℝ) ≤ 4*Real.exp (4377/32768 : ℝ)*Real.exp (-mu (radius 7 (2189/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019012803939/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2189/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0162_exp_radius
  have hrNumeric : (490547214921/500000000000 : ℝ) ≤ Real.exp (-2189/114688 : ℝ) ∧ Real.exp (-2189/114688 : ℝ) ≤ (981094429843/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490547214921/500000000000 : ℝ) ≤ (radius 7 (2189/16384 : ℝ)) ∧ (radius 7 (2189/16384 : ℝ)) ≤ (981094429843/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2189/16384 : ℝ)) (490547214921/500000000000 : ℝ) (981094429843/1000000000000 : ℝ) (96764817639/500000000000 : ℝ) (48382408821/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2189/16384 : ℝ)) (490547214921/500000000000 : ℝ) (981094429843/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2189/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490547214921/500000000000 : ℝ) (981094429843/1000000000000 : ℝ) (990547214921/1000000000000 : ℝ) (495273607461/500000000000 : ℝ) (990502109963/1000000000000 : ℝ) (247625527491/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2189/16384 : ℝ)) 1 (990547214921/1000000000000 : ℝ) (495273607461/500000000000 : ℝ) (990502109963/1000000000000 : ℝ) (247625527491/250000000000 : ℝ) (495262331221/500000000000 : ℝ) (990524662443/1000000000000 : ℝ) (198104932437/200000000000 : ℝ) (990524662187/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2189/16384 : ℝ)) 2 (495262331221/500000000000 : ℝ) (990524662443/1000000000000 : ℝ) (198104932437/200000000000 : ℝ) (990524662187/1000000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2189/16384 : ℝ)) 3 (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2189/16384 : ℝ)) 4 (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2189/16384 : ℝ)) 5 (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2189/16384 : ℝ)) 6 (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2189/16384 : ℝ)) 7 (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2189/16384 : ℝ))) (96764817639/500000000000 : ℝ) (48382408821/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2189/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96764817639/500000000000 : ℝ) (48382408821/250000000000 : ℝ) (596764817639/1000000000000 : ℝ) (298382408821/500000000000 : ℝ) (439920032821/1000000000000 : ℝ) (439920032829/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2189/16384 : ℝ))) 1 (596764817639/1000000000000 : ℝ) (298382408821/500000000000 : ℝ) (439920032821/1000000000000 : ℝ) (439920032829/1000000000000 : ℝ) (51834242523/100000000000 : ℝ) (129585606309/250000000000 : ℝ) (102475128331/200000000000 : ℝ) (256187820831/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2189/16384 : ℝ))) 2 (51834242523/100000000000 : ℝ) (129585606309/250000000000 : ℝ) (102475128331/200000000000 : ℝ) (256187820831/500000000000 : ℝ) (257679516721/500000000000 : ℝ) (515359033449/1000000000000 : ℝ) (103070079601/200000000000 : ℝ) (128837599503/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2189/16384 : ℝ))) 3 (257679516721/500000000000 : ℝ) (515359033449/1000000000000 : ℝ) (103070079601/200000000000 : ℝ) (128837599503/250000000000 : ℝ) (515354715723/1000000000000 : ℝ) (515354715731/1000000000000 : ℝ) (103070943141/200000000000 : ℝ) (515354715713/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2189/16384 : ℝ))) 4 (515354715723/1000000000000 : ℝ) (515354715731/1000000000000 : ℝ) (103070943141/200000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357857/500000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2189/16384 : ℝ))) 5 (257677357857/500000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2189/16384 : ℝ))) 6 (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2189/16384 : ℝ))) 7 (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2189/16384 : ℝ)) hmem 8 (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2189/16384 : ℝ))) hcmem 8 (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2189/16384 : ℝ)) (990524662313/1000000000000 : ℝ) (198104932463/200000000000 : ℝ) (515354715713/1000000000000 : ℝ) (257677357861/500000000000 : ℝ) (408630559761/500000000000 : ℝ) (817261119539/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0162_exp_lower
  have heNumeric : (2019012803939/1000000000000 : ℝ)/4 ≤ Real.exp (-5469485440687/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019012803939/1000000000000 : ℝ)/4 ≤ Real.exp ((4377/32768 : ℝ)-(817261119539/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4377/32768 : ℝ) (2189/16384 : ℝ) (817261119539/1000000000000 : ℝ) (2019012803939/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0163; no trusted numerical premise.
theorem cover7_leaf0163_exp_radius : (498808239744400933/500000000000000000 : ℝ) ≤ Real.exp ((-4379/229376 : ℝ)/8) ∧ Real.exp ((-4379/229376 : ℝ)/8) ≤ (997616479488801867/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4379/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0163_exp_lower : (918089168720281161/1000000000000000000 : ℝ) ≤ Real.exp ((-2734744300691/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734744300691/4000000000000 : ℝ)/8) ≤ (459044584360140581/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734744300691/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0163_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009506003127/500000000000 : ℝ) ≤ 4*Real.exp (2189/16384 : ℝ)*Real.exp (-mu (radius 7 (4379/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009506003127/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4379/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0163_exp_radius
  have hrNumeric : (981090152619/1000000000000 : ℝ) ≤ Real.exp (-4379/229376 : ℝ) ∧ Real.exp (-4379/229376 : ℝ) ≤ (49054507631/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981090152619/1000000000000 : ℝ) ≤ (radius 7 (4379/32768 : ℝ)) ∧ (radius 7 (4379/32768 : ℝ)) ≤ (49054507631/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4379/32768 : ℝ)) (981090152619/1000000000000 : ℝ) (49054507631/50000000000 : ℝ) (193551317309/1000000000000 : ℝ) (38710263463/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4379/32768 : ℝ)) (981090152619/1000000000000 : ℝ) (49054507631/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4379/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981090152619/1000000000000 : ℝ) (49054507631/50000000000 : ℝ) (990545076309/1000000000000 : ℝ) (99054507631/100000000000 : ℝ) (495249975421/500000000000 : ℝ) (247624987711/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4379/32768 : ℝ)) 1 (990545076309/1000000000000 : ℝ) (99054507631/100000000000 : ℝ) (495249975421/500000000000 : ℝ) (247624987711/250000000000 : ℝ) (39620900543/40000000000 : ℝ) (990522513577/1000000000000 : ℝ) (495261256659/500000000000 : ℝ) (990522513321/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4379/32768 : ℝ)) 2 (39620900543/40000000000 : ℝ) (990522513577/1000000000000 : ℝ) (495261256659/500000000000 : ℝ) (990522513321/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4379/32768 : ℝ)) 3 (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4379/32768 : ℝ)) 4 (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4379/32768 : ℝ)) 5 (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4379/32768 : ℝ)) 6 (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4379/32768 : ℝ)) 7 (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4379/32768 : ℝ))) (193551317309/1000000000000 : ℝ) (38710263463/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4379/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193551317309/1000000000000 : ℝ) (38710263463/200000000000 : ℝ) (298387829327/500000000000 : ℝ) (298387829329/500000000000 : ℝ) (219972337641/500000000000 : ℝ) (439944675289/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4379/32768 : ℝ))) 1 (298387829327/500000000000 : ℝ) (298387829329/500000000000 : ℝ) (219972337641/500000000000 : ℝ) (439944675289/1000000000000 : ℝ) (64795020871/125000000000 : ℝ) (259180083487/500000000000 : ℝ) (51239464611/100000000000 : ℝ) (512394646117/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4379/32768 : ℝ))) 2 (64795020871/125000000000 : ℝ) (259180083487/500000000000 : ℝ) (51239464611/100000000000 : ℝ) (512394646117/1000000000000 : ℝ) (515377406539/1000000000000 : ℝ) (257688703273/500000000000 : ℝ) (64421096883/125000000000 : ℝ) (515368775071/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4379/32768 : ℝ))) 3 (515377406539/1000000000000 : ℝ) (257688703273/500000000000 : ℝ) (64421096883/125000000000 : ℝ) (515368775071/1000000000000 : ℝ) (515373090801/1000000000000 : ℝ) (515373090809/1000000000000 : ℝ) (515373090783/1000000000000 : ℝ) (515373090791/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4379/32768 : ℝ))) 4 (515373090801/1000000000000 : ℝ) (515373090809/1000000000000 : ℝ) (515373090783/1000000000000 : ℝ) (515373090791/1000000000000 : ℝ) (64421636349/125000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4379/32768 : ℝ))) 5 (64421636349/125000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4379/32768 : ℝ))) 6 (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4379/32768 : ℝ))) 7 (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4379/32768 : ℝ)) hmem 8 (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4379/32768 : ℝ))) hcmem 8 (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4379/32768 : ℝ)) (495261256723/500000000000 : ℝ) (990522513449/1000000000000 : ℝ) (515373090791/1000000000000 : ℝ) (1288432727/2500000000 : ℝ) (408646016093/500000000000 : ℝ) (204323008051/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0163_exp_lower
  have heNumeric : (1009506003127/500000000000 : ℝ)/4 ≤ Real.exp (-2734744300691/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009506003127/500000000000 : ℝ)/4 ≤ Real.exp ((2189/16384 : ℝ)-(204323008051/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2189/16384 : ℝ) (4379/32768 : ℝ) (204323008051/250000000000 : ℝ) (1009506003127/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0164; no trusted numerical premise.
theorem cover7_leaf0164_exp_radius : (498807967915556683/500000000000000000 : ℝ) ≤ Real.exp ((-1095/57344 : ℝ)/8) ∧ Real.exp ((-1095/57344 : ℝ)/8) ≤ (997615935831113367/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1095/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0164_exp_lower : (229522280980533903/250000000000000000 : ℝ) ≤ Real.exp ((-5469491724261/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469491724261/8000000000000 : ℝ)/8) ≤ (918089123922135613/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469491724261/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0164_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019011218113/1000000000000 : ℝ) ≤ 4*Real.exp (4379/32768 : ℝ)*Real.exp (-mu (radius 7 (1095/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019011218113/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1095/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0164_exp_radius
  have hrNumeric : (196217175083/200000000000 : ℝ) ≤ Real.exp (-1095/57344 : ℝ) ∧ Real.exp (-1095/57344 : ℝ) ≤ (122635734427/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196217175083/200000000000 : ℝ) ≤ (radius 7 (1095/8192 : ℝ)) ∧ (radius 7 (1095/8192 : ℝ)) ≤ (122635734427/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1095/8192 : ℝ)) (196217175083/200000000000 : ℝ) (122635734427/125000000000 : ℝ) (2419662459/12500000000 : ℝ) (96786498363/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1095/8192 : ℝ)) (196217175083/200000000000 : ℝ) (122635734427/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1095/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196217175083/200000000000 : ℝ) (122635734427/125000000000 : ℝ) (990542937707/1000000000000 : ℝ) (247635734427/250000000000 : ℝ) (495248895863/500000000000 : ℝ) (990497791727/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1095/8192 : ℝ)) 1 (990542937707/1000000000000 : ℝ) (247635734427/250000000000 : ℝ) (495248895863/500000000000 : ℝ) (990497791727/1000000000000 : ℝ) (247630091179/250000000000 : ℝ) (495260182359/500000000000 : ℝ) (990520364459/1000000000000 : ℝ) (990520364461/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1095/8192 : ℝ)) 2 (247630091179/250000000000 : ℝ) (495260182359/500000000000 : ℝ) (990520364459/1000000000000 : ℝ) (990520364461/1000000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1095/8192 : ℝ)) 3 (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1095/8192 : ℝ)) 4 (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1095/8192 : ℝ)) 5 (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1095/8192 : ℝ)) 6 (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1095/8192 : ℝ)) 7 (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1095/8192 : ℝ))) (2419662459/12500000000 : ℝ) (96786498363/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1095/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2419662459/12500000000 : ℝ) (96786498363/500000000000 : ℝ) (14919662459/25000000000 : ℝ) (596786498363/1000000000000 : ℝ) (54996164173/125000000000 : ℝ) (27498082087/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1095/8192 : ℝ))) 1 (14919662459/25000000000 : ℝ) (596786498363/1000000000000 : ℝ) (54996164173/125000000000 : ℝ) (27498082087/62500000000 : ℝ) (32398619117/62500000000 : ℝ) (259188952939/500000000000 : ℝ) (512413647281/1000000000000 : ℝ) (64051705911/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1095/8192 : ℝ))) 2 (32398619117/62500000000 : ℝ) (259188952939/500000000000 : ℝ) (512413647281/1000000000000 : ℝ) (64051705911/125000000000 : ℝ) (8053059009/15625000000 : ℝ) (515395776583/1000000000000 : ℝ) (515387149061/1000000000000 : ℝ) (515387149069/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1095/8192 : ℝ))) 3 (8053059009/15625000000 : ℝ) (515395776583/1000000000000 : ℝ) (515387149061/1000000000000 : ℝ) (515387149069/1000000000000 : ℝ) (257695731409/500000000000 : ℝ) (257695731413/500000000000 : ℝ) (1288478657/2500000000 : ℝ) (64423932851/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1095/8192 : ℝ))) 4 (257695731409/500000000000 : ℝ) (257695731413/500000000000 : ℝ) (1288478657/2500000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462809/1000000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1095/8192 : ℝ))) 5 (515391462809/1000000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1095/8192 : ℝ))) 6 (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1095/8192 : ℝ))) 7 (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1095/8192 : ℝ)) hmem 8 (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1095/8192 : ℝ))) hcmem 8 (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1095/8192 : ℝ)) (990520364587/1000000000000 : ℝ) (99052036459/100000000000 : ℝ) (64423932851/125000000000 : ℝ) (515391462817/1000000000000 : ℝ) (204330735031/250000000000 : ℝ) (408661470071/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0164_exp_lower
  have heNumeric : (2019011218113/1000000000000 : ℝ)/4 ≤ Real.exp (-5469491724261/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019011218113/1000000000000 : ℝ)/4 ≤ Real.exp ((4379/32768 : ℝ)-(408661470071/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4379/32768 : ℝ) (1095/8192 : ℝ) (408661470071/500000000000 : ℝ) (2019011218113/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0165; no trusted numerical premise.
theorem cover7_leaf0165_exp_radius : (199523078434744227/200000000000000000 : ℝ) ≤ Real.exp ((-4381/229376 : ℝ)/8) ∧ Real.exp ((-4381/229376 : ℝ)/8) ≤ (62350962010857571/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4381/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0165_exp_lower : (459044539832488119/500000000000000000 : ℝ) ≤ Real.exp ((-1367373702357/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367373702357/2000000000000 : ℝ)/8) ≤ (918089079664976239/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367373702357/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0165_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010439489/1000000000000 : ℝ) ≤ 4*Real.exp (1095/8192 : ℝ)*Real.exp (-mu (radius 7 (4381/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010439489/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4381/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0165_exp_radius
  have hrNumeric : (981081598229/1000000000000 : ℝ) ≤ Real.exp (-4381/229376 : ℝ) ∧ Real.exp (-4381/229376 : ℝ) ≤ (98108159823/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981081598229/1000000000000 : ℝ) ≤ (radius 7 (4381/32768 : ℝ)) ∧ (radius 7 (4381/32768 : ℝ)) ≤ (98108159823/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4381/32768 : ℝ)) (981081598229/1000000000000 : ℝ) (98108159823/100000000000 : ℝ) (193594673517/1000000000000 : ℝ) (193594673523/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4381/32768 : ℝ)) (981081598229/1000000000000 : ℝ) (98108159823/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4381/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981081598229/1000000000000 : ℝ) (98108159823/100000000000 : ℝ) (495270399557/500000000000 : ℝ) (198108159823/200000000000 : ℝ) (495247816307/500000000000 : ℝ) (123811954077/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4381/32768 : ℝ)) 1 (495270399557/500000000000 : ℝ) (198108159823/200000000000 : ℝ) (495247816307/500000000000 : ℝ) (123811954077/125000000000 : ℝ) (123814776983/125000000000 : ℝ) (495259107933/500000000000 : ℝ) (495259107803/500000000000 : ℝ) (990518215609/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4381/32768 : ℝ)) 2 (123814776983/125000000000 : ℝ) (495259107933/500000000000 : ℝ) (495259107803/500000000000 : ℝ) (990518215609/1000000000000 : ℝ) (198103643147/200000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4381/32768 : ℝ)) 3 (198103643147/200000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4381/32768 : ℝ)) 4 (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4381/32768 : ℝ)) 5 (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4381/32768 : ℝ)) 6 (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4381/32768 : ℝ)) 7 (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4381/32768 : ℝ))) (193594673517/1000000000000 : ℝ) (193594673523/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4381/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193594673517/1000000000000 : ℝ) (193594673523/1000000000000 : ℝ) (298398668379/500000000000 : ℝ) (298398668381/500000000000 : ℝ) (429681589/976562500 : ℝ) (54999243393/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4381/32768 : ℝ))) 1 (298398668379/500000000000 : ℝ) (298398668381/500000000000 : ℝ) (429681589/976562500 : ℝ) (54999243393/125000000000 : ℝ) (518395641947/1000000000000 : ℝ) (518395641953/1000000000000 : ℝ) (256216322587/500000000000 : ℝ) (512432645181/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4381/32768 : ℝ))) 2 (518395641947/1000000000000 : ℝ) (518395641953/1000000000000 : ℝ) (256216322587/500000000000 : ℝ) (512432645181/1000000000000 : ℝ) (12885353589/25000000000 : ℝ) (515414143567/1000000000000 : ℝ) (515405520003/1000000000000 : ℝ) (51540552001/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4381/32768 : ℝ))) 3 (12885353589/25000000000 : ℝ) (515414143567/1000000000000 : ℝ) (515405520003/1000000000000 : ℝ) (51540552001/100000000000 : ℝ) (515409831781/1000000000000 : ℝ) (515409831789/1000000000000 : ℝ) (515409831763/1000000000000 : ℝ) (515409831771/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4381/32768 : ℝ))) 4 (515409831781/1000000000000 : ℝ) (515409831789/1000000000000 : ℝ) (515409831763/1000000000000 : ℝ) (515409831771/1000000000000 : ℝ) (128852457943/250000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4381/32768 : ℝ))) 5 (128852457943/250000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4381/32768 : ℝ))) 6 (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4381/32768 : ℝ))) 7 (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4381/32768 : ℝ)) hmem 8 (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4381/32768 : ℝ))) hcmem 8 (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4381/32768 : ℝ)) (495259107867/500000000000 : ℝ) (495259107869/500000000000 : ℝ) (515409831771/1000000000000 : ℝ) (25770491589/50000000000 : ℝ) (204338460837/250000000000 : ℝ) (408676921683/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0165_exp_lower
  have heNumeric : (2019010439489/1000000000000 : ℝ)/4 ≤ Real.exp (-1367373702357/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010439489/1000000000000 : ℝ)/4 ≤ Real.exp ((1095/8192 : ℝ)-(408676921683/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1095/8192 : ℝ) (4381/32768 : ℝ) (408676921683/500000000000 : ℝ) (2019010439489/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0166; no trusted numerical premise.
theorem cover7_leaf0166_exp_radius : (498807424258312587/500000000000000000 : ℝ) ≤ Real.exp ((-313/16384 : ℝ)/8) ∧ Real.exp ((-313/16384 : ℝ)/8) ≤ (39904593940665007/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-313/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0166_exp_lower : (918089035949262007/1000000000000000000 : ℝ) ≤ Real.exp ((-5469497856851/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469497856851/8000000000000 : ℝ)/8) ≤ (114761129493657751/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469497856851/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0166_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376208799/125000000000 : ℝ) ≤ 4*Real.exp (4381/32768 : ℝ)*Real.exp (-mu (radius 7 (2191/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (252376208799/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2191/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0166_exp_radius
  have hrNumeric : (490538660531/500000000000 : ℝ) ≤ Real.exp (-313/16384 : ℝ) ∧ Real.exp (-313/16384 : ℝ) ≤ (981077321063/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490538660531/500000000000 : ℝ) ≤ (radius 7 (2191/16384 : ℝ)) ∧ (radius 7 (2191/16384 : ℝ)) ≤ (981077321063/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2191/16384 : ℝ)) (490538660531/500000000000 : ℝ) (981077321063/1000000000000 : ℝ) (193616347697/1000000000000 : ℝ) (193616347703/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2191/16384 : ℝ)) (490538660531/500000000000 : ℝ) (981077321063/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2191/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490538660531/500000000000 : ℝ) (981077321063/1000000000000 : ℝ) (990538660531/1000000000000 : ℝ) (247634665133/250000000000 : ℝ) (247623368377/250000000000 : ℝ) (990493473509/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2191/16384 : ℝ)) 1 (990538660531/1000000000000 : ℝ) (247634665133/250000000000 : ℝ) (247623368377/250000000000 : ℝ) (990493473509/1000000000000 : ℝ) (990516067019/1000000000000 : ℝ) (990516067021/1000000000000 : ℝ) (990516066761/1000000000000 : ℝ) (990516066763/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2191/16384 : ℝ)) 2 (990516067019/1000000000000 : ℝ) (990516067021/1000000000000 : ℝ) (990516066761/1000000000000 : ℝ) (990516066763/1000000000000 : ℝ) (99051606689/100000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2191/16384 : ℝ)) 3 (99051606689/100000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2191/16384 : ℝ)) 4 (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2191/16384 : ℝ)) 5 (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2191/16384 : ℝ)) 6 (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2191/16384 : ℝ)) 7 (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2191/16384 : ℝ))) (193616347697/1000000000000 : ℝ) (193616347703/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2191/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193616347697/1000000000000 : ℝ) (193616347703/1000000000000 : ℝ) (74601021731/125000000000 : ℝ) (149202043463/250000000000 : ℝ) (55002322067/125000000000 : ℝ) (13750580517/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2191/16384 : ℝ))) 1 (74601021731/125000000000 : ℝ) (149202043463/250000000000 : ℝ) (55002322067/125000000000 : ℝ) (13750580517/31250000000 : ℝ) (64801671899/125000000000 : ℝ) (259206687599/500000000000 : ℝ) (128112909947/250000000000 : ℝ) (102490327959/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2191/16384 : ℝ))) 2 (64801671899/125000000000 : ℝ) (259206687599/500000000000 : ℝ) (128112909947/250000000000 : ℝ) (102490327959/200000000000 : ℝ) (51543250749/100000000000 : ℝ) (515432507497/1000000000000 : ℝ) (515423887887/1000000000000 : ℝ) (103084777579/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2191/16384 : ℝ))) 3 (51543250749/100000000000 : ℝ) (515432507497/1000000000000 : ℝ) (515423887887/1000000000000 : ℝ) (103084777579/200000000000 : ℝ) (64428524711/125000000000 : ℝ) (8053565589/15625000000 : ℝ) (51542819767/100000000000 : ℝ) (257714098839/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2191/16384 : ℝ))) 4 (64428524711/125000000000 : ℝ) (8053565589/15625000000 : ℝ) (51542819767/100000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197679/1000000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2191/16384 : ℝ))) 5 (515428197679/1000000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2191/16384 : ℝ))) 6 (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2191/16384 : ℝ))) 7 (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2191/16384 : ℝ)) hmem 8 (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2191/16384 : ℝ))) hcmem 8 (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2191/16384 : ℝ)) (990516066889/1000000000000 : ℝ) (247629016723/250000000000 : ℝ) (257714098839/500000000000 : ℝ) (515428197687/1000000000000 : ℝ) (408692370927/500000000000 : ℝ) (51086546367/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0166_exp_lower
  have heNumeric : (252376208799/125000000000 : ℝ)/4 ≤ Real.exp (-5469497856851/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376208799/125000000000 : ℝ)/4 ≤ Real.exp ((4381/32768 : ℝ)-(51086546367/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4381/32768 : ℝ) (2191/16384 : ℝ) (51086546367/62500000000 : ℝ) (252376208799/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0167; no trusted numerical premise.
theorem cover7_leaf0167_exp_radius : (498807152429912741/500000000000000000 : ℝ) ≤ Real.exp ((-4383/229376 : ℝ)/8) ∧ Real.exp ((-4383/229376 : ℝ)/8) ≤ (997614304859825483/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4383/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0167_exp_lower : (918088992775107601/1000000000000000000 : ℝ) ≤ Real.exp ((-2734750433261/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734750433261/4000000000000 : ℝ)/8) ≤ (459044496387553801/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734750433261/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0167_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019008910823/1000000000000 : ℝ) ≤ 4*Real.exp (2191/16384 : ℝ)*Real.exp (-mu (radius 7 (4383/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019008910823/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4383/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0167_exp_radius
  have hrNumeric : (490536521957/500000000000 : ℝ) ≤ Real.exp (-4383/229376 : ℝ) ∧ Real.exp (-4383/229376 : ℝ) ≤ (196214608783/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490536521957/500000000000 : ℝ) ≤ (radius 7 (4383/32768 : ℝ)) ∧ (radius 7 (4383/32768 : ℝ)) ≤ (196214608783/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4383/32768 : ℝ)) (490536521957/500000000000 : ℝ) (196214608783/200000000000 : ℝ) (193638019261/1000000000000 : ℝ) (193638019267/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4383/32768 : ℝ)) (490536521957/500000000000 : ℝ) (196214608783/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4383/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490536521957/500000000000 : ℝ) (196214608783/200000000000 : ℝ) (990536521957/1000000000000 : ℝ) (495268260979/500000000000 : ℝ) (495245657203/500000000000 : ℝ) (990491314407/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4383/32768 : ℝ)) 1 (990536521957/1000000000000 : ℝ) (495268260979/500000000000 : ℝ) (495245657203/500000000000 : ℝ) (990491314407/1000000000000 : ℝ) (990513918181/1000000000000 : ℝ) (990513918183/1000000000000 : ℝ) (990513917923/1000000000000 : ℝ) (39620556717/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4383/32768 : ℝ)) 2 (990513918181/1000000000000 : ℝ) (990513918183/1000000000000 : ℝ) (990513917923/1000000000000 : ℝ) (39620556717/40000000000 : ℝ) (247628479513/250000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4383/32768 : ℝ)) 3 (247628479513/250000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4383/32768 : ℝ)) 4 (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4383/32768 : ℝ)) 5 (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4383/32768 : ℝ)) 6 (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4383/32768 : ℝ)) 7 (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4383/32768 : ℝ))) (193638019261/1000000000000 : ℝ) (193638019267/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4383/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193638019261/1000000000000 : ℝ) (193638019267/1000000000000 : ℝ) (59681900963/100000000000 : ℝ) (298409504817/500000000000 : ℝ) (27502700099/62500000000 : ℝ) (55005400199/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4383/32768 : ℝ))) 1 (59681900963/100000000000 : ℝ) (298409504817/500000000000 : ℝ) (27502700099/62500000000 : ℝ) (55005400199/125000000000 : ℝ) (518431105607/1000000000000 : ℝ) (518431105613/1000000000000 : ℝ) (512470631123/1000000000000 : ℝ) (51247063113/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4383/32768 : ℝ))) 2 (518431105607/1000000000000 : ℝ) (518431105613/1000000000000 : ℝ) (512470631123/1000000000000 : ℝ) (51247063113/100000000000 : ℝ) (103090173673/200000000000 : ℝ) (128862717093/250000000000 : ℝ) (103088450543/200000000000 : ℝ) (257721126361/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4383/32768 : ℝ))) 3 (103090173673/200000000000 : ℝ) (128862717093/250000000000 : ℝ) (103088450543/200000000000 : ℝ) (257721126361/500000000000 : ℝ) (25772328027/50000000000 : ℝ) (515446560547/1000000000000 : ℝ) (515446560521/1000000000000 : ℝ) (515446560529/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4383/32768 : ℝ))) 4 (25772328027/50000000000 : ℝ) (515446560547/1000000000000 : ℝ) (515446560521/1000000000000 : ℝ) (515446560529/1000000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4383/32768 : ℝ))) 5 (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4383/32768 : ℝ))) 6 (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4383/32768 : ℝ))) 7 (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4383/32768 : ℝ)) hmem 8 (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4383/32768 : ℝ))) hcmem 8 (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4383/32768 : ℝ)) (990513918051/1000000000000 : ℝ) (495256959027/500000000000 : ℝ) (51544656053/100000000000 : ℝ) (257723280269/500000000000 : ℝ) (817415635643/1000000000000 : ℝ) (817415635659/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0167_exp_lower
  have heNumeric : (2019008910823/1000000000000 : ℝ)/4 ≤ Real.exp (-2734750433261/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019008910823/1000000000000 : ℝ)/4 ≤ Real.exp ((2191/16384 : ℝ)-(817415635659/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2191/16384 : ℝ) (4383/32768 : ℝ) (817415635659/1000000000000 : ℝ) (2019008910823/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0168; no trusted numerical premise.
theorem cover7_leaf0168_exp_radius : (49880688060166103/50000000000000000 : ℝ) ≤ Real.exp ((-137/7168 : ℝ)/8) ∧ Real.exp ((-137/7168 : ℝ)/8) ≤ (997613761203322061/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-137/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0168_exp_lower : (918088950141250573/1000000000000000000 : ℝ) ≤ Real.exp ((-5469503838529/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469503838529/8000000000000 : ℝ)/8) ≤ (459044475070625287/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469503838529/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0168_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (50475204019/25000000000 : ℝ) ≤ 4*Real.exp (4383/32768 : ℝ)*Real.exp (-mu (radius 7 (137/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (50475204019/25000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (137/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0168_exp_radius
  have hrNumeric : (15329199481/15625000000 : ℝ) ≤ Real.exp (-137/7168 : ℝ) ∧ Real.exp (-137/7168 : ℝ) ≤ (196213753357/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15329199481/15625000000 : ℝ) ≤ (radius 7 (137/1024 : ℝ)) ∧ (radius 7 (137/1024 : ℝ)) ≤ (196213753357/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (137/1024 : ℝ)) (15329199481/15625000000 : ℝ) (196213753357/200000000000 : ℝ) (193659688213/1000000000000 : ℝ) (193659688219/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (137/1024 : ℝ)) (15329199481/15625000000 : ℝ) (196213753357/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (137/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15329199481/15625000000 : ℝ) (196213753357/200000000000 : ℝ) (30954199481/31250000000 : ℝ) (990534383393/1000000000000 : ℝ) (247622288827/250000000000 : ℝ) (99048915531/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (137/1024 : ℝ)) 1 (30954199481/31250000000 : ℝ) (990534383393/1000000000000 : ℝ) (247622288827/250000000000 : ℝ) (99048915531/100000000000 : ℝ) (19810235387/20000000000 : ℝ) (123813971169/125000000000 : ℝ) (990511769091/1000000000000 : ℝ) (495255884547/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (137/1024 : ℝ)) 2 (19810235387/20000000000 : ℝ) (123813971169/125000000000 : ℝ) (990511769091/1000000000000 : ℝ) (495255884547/500000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (137/1024 : ℝ)) 3 (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (137/1024 : ℝ)) 4 (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (137/1024 : ℝ)) 5 (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (137/1024 : ℝ)) 6 (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (137/1024 : ℝ)) 7 (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (137/1024 : ℝ))) (193659688213/1000000000000 : ℝ) (193659688219/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (137/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193659688213/1000000000000 : ℝ) (193659688219/1000000000000 : ℝ) (298414922053/500000000000 : ℝ) (59682984411/100000000000 : ℝ) (440067822287/1000000000000 : ℝ) (88013564459/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (137/1024 : ℝ))) 1 (298414922053/500000000000 : ℝ) (59682984411/100000000000 : ℝ) (440067822287/1000000000000 : ℝ) (88013564459/200000000000 : ℝ) (129612208299/250000000000 : ℝ) (518448833203/1000000000000 : ℝ) (32030601199/62500000000 : ℝ) (512489619191/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (137/1024 : ℝ))) 2 (129612208299/250000000000 : ℝ) (518448833203/1000000000000 : ℝ) (32030601199/62500000000 : ℝ) (512489619191/1000000000000 : ℝ) (51546922619/100000000000 : ℝ) (515469226197/1000000000000 : ℝ) (51546061449/100000000000 : ℝ) (257730307249/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (137/1024 : ℝ))) 3 (51546922619/100000000000 : ℝ) (515469226197/1000000000000 : ℝ) (51546061449/100000000000 : ℝ) (257730307249/500000000000 : ℝ) (25773246017/50000000000 : ℝ) (128866230087/250000000000 : ℝ) (257732460161/500000000000 : ℝ) (51546492033/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (137/1024 : ℝ))) 4 (25773246017/50000000000 : ℝ) (128866230087/250000000000 : ℝ) (257732460161/500000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920331/1000000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (137/1024 : ℝ))) 5 (515464920331/1000000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (137/1024 : ℝ))) 6 (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (137/1024 : ℝ))) 7 (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (137/1024 : ℝ)) hmem 8 (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (137/1024 : ℝ))) hcmem 8 (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (137/1024 : ℝ)) (49525588461/50000000000 : ℝ) (990511769223/1000000000000 : ℝ) (51546492033/100000000000 : ℝ) (515464920339/1000000000000 : ℝ) (10218081559/12500000000 : ℝ) (408723262369/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0168_exp_lower
  have heNumeric : (50475204019/25000000000 : ℝ)/4 ≤ Real.exp (-5469503838529/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (50475204019/25000000000 : ℝ)/4 ≤ Real.exp ((4383/32768 : ℝ)-(408723262369/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4383/32768 : ℝ) (137/1024 : ℝ) (408723262369/500000000000 : ℝ) (50475204019/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0169; no trusted numerical premise.
theorem cover7_leaf0169_exp_radius : (249403304386778727/250000000000000000 : ℝ) ≤ Real.exp ((-4385/229376 : ℝ)/8) ∧ Real.exp ((-4385/229376 : ℝ)/8) ≤ (997613217547114909/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4385/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0169_exp_lower : (459044454024189707/500000000000000000 : ℝ) ≤ Real.exp ((-683688346603/1000000000000 : ℝ)/8) ∧ Real.exp ((-683688346603/1000000000000 : ℝ)/8) ≤ (183617781609675883/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683688346603/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0169_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009503710107/500000000000 : ℝ) ≤ 4*Real.exp (137/1024 : ℝ)*Real.exp (-mu (radius 7 (4385/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009503710107/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4385/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0169_exp_radius
  have hrNumeric : (981064489673/1000000000000 : ℝ) ≤ Real.exp (-4385/229376 : ℝ) ∧ Real.exp (-4385/229376 : ℝ) ≤ (490532244837/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981064489673/1000000000000 : ℝ) ≤ (radius 7 (4385/32768 : ℝ)) ∧ (radius 7 (4385/32768 : ℝ)) ≤ (490532244837/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4385/32768 : ℝ)) (981064489673/1000000000000 : ℝ) (490532244837/500000000000 : ℝ) (3873627091/20000000000 : ℝ) (193681354557/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4385/32768 : ℝ)) (981064489673/1000000000000 : ℝ) (490532244837/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4385/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981064489673/1000000000000 : ℝ) (490532244837/500000000000 : ℝ) (247633061209/250000000000 : ℝ) (990532244837/1000000000000 : ℝ) (123810874527/125000000000 : ℝ) (990486996217/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4385/32768 : ℝ)) 1 (247633061209/250000000000 : ℝ) (990532244837/1000000000000 : ℝ) (123810874527/125000000000 : ℝ) (990486996217/1000000000000 : ℝ) (495254810263/500000000000 : ℝ) (990509620527/1000000000000 : ℝ) (990509620267/1000000000000 : ℝ) (990509620269/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4385/32768 : ℝ)) 2 (495254810263/500000000000 : ℝ) (990509620527/1000000000000 : ℝ) (990509620267/1000000000000 : ℝ) (990509620269/1000000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4385/32768 : ℝ)) 3 (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4385/32768 : ℝ)) 4 (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4385/32768 : ℝ)) 5 (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4385/32768 : ℝ)) 6 (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4385/32768 : ℝ)) 7 (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4385/32768 : ℝ))) (3873627091/20000000000 : ℝ) (193681354557/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4385/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3873627091/20000000000 : ℝ) (193681354557/1000000000000 : ℝ) (23873627091/40000000000 : ℝ) (596840677279/1000000000000 : ℝ) (220046219321/500000000000 : ℝ) (440092438651/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4385/32768 : ℝ))) 1 (23873627091/40000000000 : ℝ) (596840677279/1000000000000 : ℝ) (220046219321/500000000000 : ℝ) (440092438651/1000000000000 : ℝ) (259233278979/500000000000 : ℝ) (103693311593/200000000000 : ℝ) (512508603969/1000000000000 : ℝ) (512508603977/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4385/32768 : ℝ))) 2 (259233278979/500000000000 : ℝ) (103693311593/200000000000 : ℝ) (512508603969/1000000000000 : ℝ) (512508603977/1000000000000 : ℝ) (515487580963/1000000000000 : ℝ) (515487580971/1000000000000 : ℝ) (515478973211/1000000000000 : ℝ) (25773948661/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4385/32768 : ℝ))) 3 (515487580963/1000000000000 : ℝ) (515487580971/1000000000000 : ℝ) (515478973211/1000000000000 : ℝ) (25773948661/50000000000 : ℝ) (515483277087/1000000000000 : ℝ) (64435409637/125000000000 : ℝ) (515483277069/1000000000000 : ℝ) (257741638539/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4385/32768 : ℝ))) 4 (515483277087/1000000000000 : ℝ) (64435409637/125000000000 : ℝ) (515483277069/1000000000000 : ℝ) (257741638539/500000000000 : ℝ) (257741638539/500000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4385/32768 : ℝ))) 5 (257741638539/500000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4385/32768 : ℝ))) 6 (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4385/32768 : ℝ))) 7 (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4385/32768 : ℝ)) hmem 8 (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4385/32768 : ℝ))) hcmem 8 (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4385/32768 : ℝ)) (247627405099/250000000000 : ℝ) (495254810199/500000000000 : ℝ) (515483277077/1000000000000 : ℝ) (515483277087/1000000000000 : ℝ) (163495481817/200000000000 : ℝ) (817477409103/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0169_exp_lower
  have heNumeric : (1009503710107/500000000000 : ℝ)/4 ≤ Real.exp (-683688346603/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009503710107/500000000000 : ℝ)/4 ≤ Real.exp ((137/1024 : ℝ)-(817477409103/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (137/1024 : ℝ) (4385/32768 : ℝ) (817477409103/1000000000000 : ℝ) (1009503710107/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0170; no trusted numerical premise.
theorem cover7_leaf0170_exp_radius : (124701584236400503/125000000000000000 : ℝ) ≤ Real.exp ((-2193/114688 : ℝ)/8) ∧ Real.exp ((-2193/114688 : ℝ)/8) ≤ (39904506955648161/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2193/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0170_exp_lower : (114761108312047411/125000000000000000 : ℝ) ≤ Real.exp ((-1093901933883/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093901933883/1600000000000 : ℝ)/8) ≤ (918088866496379289/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093901933883/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0170_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (63093959037/31250000000 : ℝ) ≤ 4*Real.exp (4385/32768 : ℝ)*Real.exp (-mu (radius 7 (2193/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (63093959037/31250000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2193/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0170_exp_radius
  have hrNumeric : (981060212581/1000000000000 : ℝ) ≤ Real.exp (-2193/114688 : ℝ) ∧ Real.exp (-2193/114688 : ℝ) ≤ (490530106291/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981060212581/1000000000000 : ℝ) ≤ (radius 7 (2193/16384 : ℝ)) ∧ (radius 7 (2193/16384 : ℝ)) ≤ (490530106291/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2193/16384 : ℝ)) (981060212581/1000000000000 : ℝ) (490530106291/500000000000 : ℝ) (96851509137/500000000000 : ℝ) (4842575457/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2193/16384 : ℝ)) (981060212581/1000000000000 : ℝ) (490530106291/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2193/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981060212581/1000000000000 : ℝ) (490530106291/500000000000 : ℝ) (99053010629/100000000000 : ℝ) (990530106291/1000000000000 : ℝ) (123810604641/125000000000 : ℝ) (990484837129/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2193/16384 : ℝ)) 1 (99053010629/100000000000 : ℝ) (990530106291/1000000000000 : ℝ) (123810604641/125000000000 : ℝ) (990484837129/1000000000000 : ℝ) (990507471709/1000000000000 : ℝ) (99050747171/100000000000 : ℝ) (19810149429/20000000000 : ℝ) (247626867863/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2193/16384 : ℝ)) 2 (990507471709/1000000000000 : ℝ) (99050747171/100000000000 : ℝ) (19810149429/20000000000 : ℝ) (247626867863/250000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2193/16384 : ℝ)) 3 (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2193/16384 : ℝ)) 4 (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2193/16384 : ℝ)) 5 (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2193/16384 : ℝ)) 6 (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2193/16384 : ℝ)) 7 (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2193/16384 : ℝ))) (96851509137/500000000000 : ℝ) (4842575457/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2193/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (96851509137/500000000000 : ℝ) (4842575457/25000000000 : ℝ) (596851509137/1000000000000 : ℝ) (29842575457/50000000000 : ℝ) (440117050651/1000000000000 : ℝ) (440117050659/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2193/16384 : ℝ))) 1 (596851509137/1000000000000 : ℝ) (29842575457/50000000000 : ℝ) (440117050651/1000000000000 : ℝ) (440117050659/1000000000000 : ℝ) (259242139947/500000000000 : ℝ) (5184842799/10000000000 : ℝ) (12813189637/25000000000 : ℝ) (256263792743/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2193/16384 : ℝ))) 2 (259242139947/500000000000 : ℝ) (5184842799/10000000000 : ℝ) (12813189637/25000000000 : ℝ) (256263792743/500000000000 : ℝ) (515505932687/1000000000000 : ℝ) (515505932693/1000000000000 : ℝ) (6443716611/12500000000 : ℝ) (515497328887/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2193/16384 : ℝ))) 3 (515505932687/1000000000000 : ℝ) (515505932693/1000000000000 : ℝ) (6443716611/12500000000 : ℝ) (515497328887/1000000000000 : ℝ) (515501630783/1000000000000 : ℝ) (51550163079/100000000000 : ℝ) (103100326153/200000000000 : ℝ) (515501630773/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2193/16384 : ℝ))) 4 (515501630783/1000000000000 : ℝ) (51550163079/100000000000 : ℝ) (103100326153/200000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815387/500000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2193/16384 : ℝ))) 5 (257750815387/500000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2193/16384 : ℝ))) 6 (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2193/16384 : ℝ))) 7 (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2193/16384 : ℝ)) hmem 8 (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2193/16384 : ℝ))) hcmem 8 (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2193/16384 : ℝ)) (990507471579/1000000000000 : ℝ) (990507471581/1000000000000 : ℝ) (515501630773/1000000000000 : ℝ) (257750815391/500000000000 : ℝ) (408754144369/500000000000 : ℝ) (163501657751/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0170_exp_lower
  have heNumeric : (63093959037/31250000000 : ℝ)/4 ≤ Real.exp (-1093901933883/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (63093959037/31250000000 : ℝ)/4 ≤ Real.exp ((4385/32768 : ℝ)-(163501657751/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4385/32768 : ℝ) (2193/16384 : ℝ) (163501657751/200000000000 : ℝ) (63093959037/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0171; no trusted numerical premise.
theorem cover7_leaf0171_exp_radius : (997612130235589409/1000000000000000000 : ℝ) ≤ Real.exp ((-4387/229376 : ℝ)/8) ∧ Real.exp ((-4387/229376 : ℝ)/8) ≤ (99761213023558941/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4387/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0171_exp_lower : (229522206370968247/250000000000000000 : ℝ) ≤ Real.exp ((-2734756264199/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734756264199/4000000000000 : ℝ)/8) ≤ (918088825483872989/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734756264199/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0171_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009502983823/500000000000 : ℝ) ≤ 4*Real.exp (2193/16384 : ℝ)*Real.exp (-mu (radius 7 (4387/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009502983823/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4387/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0171_exp_radius
  have hrNumeric : (981055935507/1000000000000 : ℝ) ≤ Real.exp (-4387/229376 : ℝ) ∧ Real.exp (-4387/229376 : ℝ) ≤ (245263983877/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981055935507/1000000000000 : ℝ) ≤ (radius 7 (4387/32768 : ℝ)) ∧ (radius 7 (4387/32768 : ℝ)) ≤ (245263983877/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4387/32768 : ℝ)) (981055935507/1000000000000 : ℝ) (245263983877/250000000000 : ℝ) (193724679389/1000000000000 : ℝ) (38744935879/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4387/32768 : ℝ)) (981055935507/1000000000000 : ℝ) (245263983877/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4387/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981055935507/1000000000000 : ℝ) (245263983877/250000000000 : ℝ) (990527967753/1000000000000 : ℝ) (495263983877/500000000000 : ℝ) (247620669511/250000000000 : ℝ) (495241339023/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4387/32768 : ℝ)) 1 (990527967753/1000000000000 : ℝ) (495263983877/500000000000 : ℝ) (247620669511/250000000000 : ℝ) (495241339023/500000000000 : ℝ) (495252661449/500000000000 : ℝ) (9905053229/10000000000 : ℝ) (990505322639/1000000000000 : ℝ) (495252661321/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4387/32768 : ℝ)) 2 (495252661449/500000000000 : ℝ) (9905053229/10000000000 : ℝ) (990505322639/1000000000000 : ℝ) (495252661321/500000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4387/32768 : ℝ)) 3 (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4387/32768 : ℝ)) 4 (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4387/32768 : ℝ)) 5 (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4387/32768 : ℝ)) 6 (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4387/32768 : ℝ)) 7 (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4387/32768 : ℝ))) (193724679389/1000000000000 : ℝ) (38744935879/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4387/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193724679389/1000000000000 : ℝ) (38744935879/200000000000 : ℝ) (298431169847/500000000000 : ℝ) (298431169849/500000000000 : ℝ) (5501770729/12500000000 : ℝ) (55017707291/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4387/32768 : ℝ))) 1 (298431169847/500000000000 : ℝ) (298431169849/500000000000 : ℝ) (5501770729/12500000000 : ℝ) (55017707291/125000000000 : ℝ) (518501999007/1000000000000 : ℝ) (518501999013/1000000000000 : ℝ) (12813664093/25000000000 : ℝ) (512546563727/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4387/32768 : ℝ))) 2 (518501999007/1000000000000 : ℝ) (518501999013/1000000000000 : ℝ) (12813664093/25000000000 : ℝ) (512546563727/1000000000000 : ℝ) (515524281363/1000000000000 : ℝ) (51552428137/100000000000 : ℝ) (1031031363/2000000000 : ℝ) (128878920377/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4387/32768 : ℝ))) 3 (515524281363/1000000000000 : ℝ) (51552428137/100000000000 : ℝ) (1031031363/2000000000 : ℝ) (128878920377/250000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981439/1000000000000 : ℝ) (515519981413/1000000000000 : ℝ) (257759990711/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4387/32768 : ℝ))) 4 (515519981431/1000000000000 : ℝ) (515519981439/1000000000000 : ℝ) (515519981413/1000000000000 : ℝ) (257759990711/500000000000 : ℝ) (257759990711/500000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4387/32768 : ℝ))) 5 (257759990711/500000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4387/32768 : ℝ))) 6 (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4387/32768 : ℝ))) 7 (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4387/32768 : ℝ)) hmem 8 (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4387/32768 : ℝ))) hcmem 8 (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4387/32768 : ℝ)) (61906582673/62500000000 : ℝ) (990505322771/1000000000000 : ℝ) (515519981421/1000000000000 : ℝ) (515519981431/1000000000000 : ℝ) (408769581843/500000000000 : ℝ) (408769581853/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0171_exp_lower
  have heNumeric : (1009502983823/500000000000 : ℝ)/4 ≤ Real.exp (-2734756264199/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009502983823/500000000000 : ℝ)/4 ≤ Real.exp ((2193/16384 : ℝ)-(408769581853/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2193/16384 : ℝ) (4387/32768 : ℝ) (408769581853/500000000000 : ℝ) (1009502983823/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0172; no trusted numerical premise.
theorem cover7_leaf0172_exp_radius : (498805793290135531/500000000000000000 : ℝ) ≤ Real.exp ((-1097/57344 : ℝ)/8) ∧ Real.exp ((-1097/57344 : ℝ)/8) ≤ (997611586580271063/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1097/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0172_exp_lower : (918088785011893293/1000000000000000000 : ℝ) ≤ Real.exp ((-5469515349701/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469515349701/8000000000000 : ℝ)/8) ≤ (459044392505946647/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469515349701/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0172_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009502627809/500000000000 : ℝ) ≤ 4*Real.exp (4387/32768 : ℝ)*Real.exp (-mu (radius 7 (1097/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009502627809/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1097/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0172_exp_radius
  have hrNumeric : (245262914613/250000000000 : ℝ) ≤ Real.exp (-1097/57344 : ℝ) ∧ Real.exp (-1097/57344 : ℝ) ≤ (981051658453/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245262914613/250000000000 : ℝ) ≤ (radius 7 (1097/8192 : ℝ)) ∧ (radius 7 (1097/8192 : ℝ)) ≤ (981051658453/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1097/8192 : ℝ)) (245262914613/250000000000 : ℝ) (981051658453/1000000000000 : ℝ) (48436584473/250000000000 : ℝ) (96873168949/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1097/8192 : ℝ)) (245262914613/250000000000 : ℝ) (981051658453/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1097/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245262914613/250000000000 : ℝ) (981051658453/1000000000000 : ℝ) (495262914613/500000000000 : ℝ) (990525829227/1000000000000 : ℝ) (495240259483/500000000000 : ℝ) (990480518967/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1097/8192 : ℝ)) 1 (495262914613/500000000000 : ℝ) (990525829227/1000000000000 : ℝ) (495240259483/500000000000 : ℝ) (990480518967/1000000000000 : ℝ) (61906448381/62500000000 : ℝ) (990503174097/1000000000000 : ℝ) (247625793459/250000000000 : ℝ) (495251586919/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1097/8192 : ℝ)) 2 (61906448381/62500000000 : ℝ) (990503174097/1000000000000 : ℝ) (247625793459/250000000000 : ℝ) (495251586919/500000000000 : ℝ) (495251586983/500000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1097/8192 : ℝ)) 3 (495251586983/500000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1097/8192 : ℝ)) 4 (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1097/8192 : ℝ)) 5 (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1097/8192 : ℝ)) 6 (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1097/8192 : ℝ)) 7 (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1097/8192 : ℝ))) (48436584473/250000000000 : ℝ) (96873168949/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1097/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48436584473/250000000000 : ℝ) (96873168949/500000000000 : ℝ) (298436584473/500000000000 : ℝ) (596873168949/1000000000000 : ℝ) (220083130823/500000000000 : ℝ) (220083130827/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1097/8192 : ℝ))) 1 (298436584473/500000000000 : ℝ) (596873168949/1000000000000 : ℝ) (220083130823/500000000000 : ℝ) (220083130827/500000000000 : ℝ) (16203741103/31250000000 : ℝ) (259259857651/500000000000 : ℝ) (512565538689/1000000000000 : ℝ) (64070692337/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1097/8192 : ℝ))) 2 (16203741103/31250000000 : ℝ) (259259857651/500000000000 : ℝ) (512565538689/1000000000000 : ℝ) (64070692337/125000000000 : ℝ) (32221414187/62500000000 : ℝ) (515542626999/1000000000000 : ℝ) (51553403107/100000000000 : ℝ) (515534031077/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1097/8192 : ℝ))) 3 (32221414187/62500000000 : ℝ) (515542626999/1000000000000 : ℝ) (51553403107/100000000000 : ℝ) (515534031077/1000000000000 : ℝ) (515538329031/1000000000000 : ℝ) (257769164519/500000000000 : ℝ) (515538329013/1000000000000 : ℝ) (515538329021/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1097/8192 : ℝ))) 4 (515538329031/1000000000000 : ℝ) (257769164519/500000000000 : ℝ) (515538329013/1000000000000 : ℝ) (515538329021/1000000000000 : ℝ) (257769164511/500000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1097/8192 : ℝ))) 5 (257769164511/500000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1097/8192 : ℝ))) 6 (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1097/8192 : ℝ))) 7 (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1097/8192 : ℝ)) hmem 8 (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1097/8192 : ℝ))) hcmem 8 (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1097/8192 : ℝ)) (198100634793/200000000000 : ℝ) (61906448373/62500000000 : ℝ) (515538329021/1000000000000 : ℝ) (51553832903/100000000000 : ℝ) (817570033929/1000000000000 : ℝ) (817570033947/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0172_exp_lower
  have heNumeric : (1009502627809/500000000000 : ℝ)/4 ≤ Real.exp (-5469515349701/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009502627809/500000000000 : ℝ)/4 ≤ Real.exp ((4387/32768 : ℝ)-(817570033947/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4387/32768 : ℝ) (1097/8192 : ℝ) (817570033947/1000000000000 : ℝ) (1009502627809/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0173; no trusted numerical premise.
theorem cover7_leaf0173_exp_radius : (199522208585049797/200000000000000000 : ℝ) ≤ Real.exp ((-627/32768 : ℝ)/8) ∧ Real.exp ((-627/32768 : ℝ)/8) ≤ (498805521462624493/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-627/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0173_exp_lower : (11476109313492591/12500000000000000 : ℝ) ≤ Real.exp ((-1367379533349/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367379533349/2000000000000 : ℝ)/8) ≤ (918088745079407281/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367379533349/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0173_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019004553081/1000000000000 : ℝ) ≤ 4*Real.exp (1097/8192 : ℝ)*Real.exp (-mu (radius 7 (4389/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019004553081/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4389/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0173_exp_radius
  have hrNumeric : (196209476283/200000000000 : ℝ) ≤ Real.exp (-627/32768 : ℝ) ∧ Real.exp (-627/32768 : ℝ) ≤ (122630922677/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196209476283/200000000000 : ℝ) ≤ (radius 7 (4389/32768 : ℝ)) ∧ (radius 7 (4389/32768 : ℝ)) ≤ (122630922677/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4389/32768 : ℝ)) (196209476283/200000000000 : ℝ) (122630922677/125000000000 : ℝ) (48441998447/250000000000 : ℝ) (96883996897/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4389/32768 : ℝ)) (196209476283/200000000000 : ℝ) (122630922677/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4389/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196209476283/200000000000 : ℝ) (122630922677/125000000000 : ℝ) (990523690707/1000000000000 : ℝ) (247630922677/250000000000 : ℝ) (247619589973/250000000000 : ℝ) (990478359893/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4389/32768 : ℝ)) 1 (990523690707/1000000000000 : ℝ) (247630922677/250000000000 : ℝ) (247619589973/250000000000 : ℝ) (990478359893/1000000000000 : ℝ) (990501025299/1000000000000 : ℝ) (990501025301/1000000000000 : ℝ) (12381262813/12500000000 : ℝ) (495250512521/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4389/32768 : ℝ)) 2 (990501025299/1000000000000 : ℝ) (990501025301/1000000000000 : ℝ) (12381262813/12500000000 : ℝ) (495250512521/500000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4389/32768 : ℝ)) 3 (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4389/32768 : ℝ)) 4 (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4389/32768 : ℝ)) 5 (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4389/32768 : ℝ)) 6 (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4389/32768 : ℝ)) 7 (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4389/32768 : ℝ))) (48441998447/250000000000 : ℝ) (96883996897/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4389/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48441998447/250000000000 : ℝ) (96883996897/500000000000 : ℝ) (298441998447/500000000000 : ℝ) (596883996897/1000000000000 : ℝ) (110047715159/250000000000 : ℝ) (110047715161/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4389/32768 : ℝ))) 1 (298441998447/500000000000 : ℝ) (596883996897/1000000000000 : ℝ) (110047715159/250000000000 : ℝ) (110047715161/250000000000 : ℝ) (103707485753/200000000000 : ℝ) (518537428771/1000000000000 : ℝ) (51258451039/100000000000 : ℝ) (512584510397/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4389/32768 : ℝ))) 2 (103707485753/200000000000 : ℝ) (518537428771/1000000000000 : ℝ) (51258451039/100000000000 : ℝ) (512584510397/1000000000000 : ℝ) (515560969577/1000000000000 : ℝ) (32222560599/62500000000 : ℝ) (515552377593/1000000000000 : ℝ) (515552377601/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4389/32768 : ℝ))) 3 (515560969577/1000000000000 : ℝ) (32222560599/62500000000 : ℝ) (515552377593/1000000000000 : ℝ) (515552377601/1000000000000 : ℝ) (103111334717/200000000000 : ℝ) (515556673593/1000000000000 : ℝ) (515556673567/1000000000000 : ℝ) (20622266943/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4389/32768 : ℝ))) 4 (103111334717/200000000000 : ℝ) (515556673593/1000000000000 : ℝ) (515556673567/1000000000000 : ℝ) (20622266943/40000000000 : ℝ) (64444584197/125000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4389/32768 : ℝ))) 5 (64444584197/125000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4389/32768 : ℝ))) 6 (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4389/32768 : ℝ))) 7 (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4389/32768 : ℝ)) hmem 8 (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4389/32768 : ℝ))) hcmem 8 (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4389/32768 : ℝ)) (990501025169/1000000000000 : ℝ) (247625256293/250000000000 : ℝ) (20622266943/40000000000 : ℝ) (32222292099/62500000000 : ℝ) (817600899469/1000000000000 : ℝ) (817600899487/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0173_exp_lower
  have heNumeric : (2019004553081/1000000000000 : ℝ)/4 ≤ Real.exp (-1367379533349/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019004553081/1000000000000 : ℝ)/4 ≤ Real.exp ((1097/8192 : ℝ)-(817600899487/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1097/8192 : ℝ) (4389/32768 : ℝ) (817600899487/1000000000000 : ℝ) (2019004553081/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0174; no trusted numerical premise.
theorem cover7_leaf0174_exp_radius : (39904419970820927/40000000000000000 : ℝ) ≤ Real.exp ((-2195/114688 : ℝ)/8) ∧ Real.exp ((-2195/114688 : ℝ)/8) ≤ (124701312408815397/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2195/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0174_exp_lower : (114761088210916621/125000000000000000 : ℝ) ≤ Real.exp ((-5469520879419/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469520879419/8000000000000 : ℝ)/8) ≤ (918088705687332969/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469520879419/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0174_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504750965013/250000000000 : ℝ) ≤ 4*Real.exp (4389/32768 : ℝ)*Real.exp (-mu (radius 7 (2195/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (504750965013/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2195/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0174_exp_radius
  have hrNumeric : (490521552199/500000000000 : ℝ) ≤ Real.exp (-2195/114688 : ℝ) ∧ Real.exp (-2195/114688 : ℝ) ≤ (981043104399/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490521552199/500000000000 : ℝ) ≤ (radius 7 (2195/16384 : ℝ)) ∧ (radius 7 (2195/16384 : ℝ)) ≤ (981043104399/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2195/16384 : ℝ)) (490521552199/500000000000 : ℝ) (981043104399/1000000000000 : ℝ) (193789647069/1000000000000 : ℝ) (7751585883/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2195/16384 : ℝ)) (490521552199/500000000000 : ℝ) (981043104399/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2195/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490521552199/500000000000 : ℝ) (981043104399/1000000000000 : ℝ) (990521552199/1000000000000 : ℝ) (4952607761/5000000000 : ℝ) (990476200823/1000000000000 : ℝ) (39619048033/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2195/16384 : ℝ)) 1 (990521552199/1000000000000 : ℝ) (4952607761/5000000000 : ℝ) (990476200823/1000000000000 : ℝ) (39619048033/40000000000 : ℝ) (990498876511/1000000000000 : ℝ) (990498876513/1000000000000 : ℝ) (990498876251/1000000000000 : ℝ) (990498876253/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2195/16384 : ℝ)) 2 (990498876511/1000000000000 : ℝ) (990498876513/1000000000000 : ℝ) (990498876251/1000000000000 : ℝ) (990498876253/1000000000000 : ℝ) (990498876381/1000000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2195/16384 : ℝ)) 3 (990498876381/1000000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2195/16384 : ℝ)) 4 (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2195/16384 : ℝ)) 5 (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2195/16384 : ℝ)) 6 (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2195/16384 : ℝ)) 7 (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2195/16384 : ℝ))) (193789647069/1000000000000 : ℝ) (7751585883/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2195/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (193789647069/1000000000000 : ℝ) (7751585883/40000000000 : ℝ) (298447411767/500000000000 : ℝ) (298447411769/500000000000 : ℝ) (440215455281/1000000000000 : ℝ) (440215455289/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2195/16384 : ℝ))) 1 (298447411767/500000000000 : ℝ) (298447411769/500000000000 : ℝ) (440215455281/1000000000000 : ℝ) (440215455289/1000000000000 : ℝ) (518555139407/1000000000000 : ℝ) (259277569707/500000000000 : ℝ) (256301739409/500000000000 : ℝ) (20504139153/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2195/16384 : ℝ))) 2 (518555139407/1000000000000 : ℝ) (259277569707/500000000000 : ℝ) (256301739409/500000000000 : ℝ) (20504139153/40000000000 : ℝ) (64447413639/125000000000 : ℝ) (1611185341/3125000000 : ℝ) (64446340133/125000000000 : ℝ) (32223170067/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2195/16384 : ℝ))) 3 (64447413639/125000000000 : ℝ) (1611185341/3125000000 : ℝ) (64446340133/125000000000 : ℝ) (32223170067/62500000000 : ℝ) (32223438443/62500000000 : ℝ) (64446876887/125000000000 : ℝ) (51557501507/100000000000 : ℝ) (515575015079/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2195/16384 : ℝ))) 4 (32223438443/62500000000 : ℝ) (64446876887/125000000000 : ℝ) (51557501507/100000000000 : ℝ) (515575015079/1000000000000 : ℝ) (515575015079/1000000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2195/16384 : ℝ))) 5 (515575015079/1000000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2195/16384 : ℝ))) 6 (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2195/16384 : ℝ))) 7 (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2195/16384 : ℝ)) hmem 8 (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2195/16384 : ℝ))) hcmem 8 (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2195/16384 : ℝ)) (49524943819/50000000000 : ℝ) (990498876383/1000000000000 : ℝ) (257787507539/500000000000 : ℝ) (32223438443/62500000000 : ℝ) (817631760299/1000000000000 : ℝ) (408815880159/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0174_exp_lower
  have heNumeric : (504750965013/250000000000 : ℝ)/4 ≤ Real.exp (-5469520879419/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504750965013/250000000000 : ℝ)/4 ≤ Real.exp ((4389/32768 : ℝ)-(408815880159/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4389/32768 : ℝ) (2195/16384 : ℝ) (408815880159/500000000000 : ℝ) (504750965013/250000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0150_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0150_certificate
#check SmaleRate.Proofs.cover7_leaf0151_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0151_certificate
#check SmaleRate.Proofs.cover7_leaf0152_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0152_certificate
#check SmaleRate.Proofs.cover7_leaf0153_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0153_certificate
#check SmaleRate.Proofs.cover7_leaf0154_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0154_certificate
#check SmaleRate.Proofs.cover7_leaf0155_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0155_certificate
#check SmaleRate.Proofs.cover7_leaf0156_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0156_certificate
#check SmaleRate.Proofs.cover7_leaf0157_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0157_certificate
#check SmaleRate.Proofs.cover7_leaf0158_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0158_certificate
#check SmaleRate.Proofs.cover7_leaf0159_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0159_certificate
#check SmaleRate.Proofs.cover7_leaf0160_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0160_certificate
#check SmaleRate.Proofs.cover7_leaf0161_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0161_certificate
#check SmaleRate.Proofs.cover7_leaf0162_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0162_certificate
#check SmaleRate.Proofs.cover7_leaf0163_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0163_certificate
#check SmaleRate.Proofs.cover7_leaf0164_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0164_certificate
#check SmaleRate.Proofs.cover7_leaf0165_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0165_certificate
#check SmaleRate.Proofs.cover7_leaf0166_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0166_certificate
#check SmaleRate.Proofs.cover7_leaf0167_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0167_certificate
#check SmaleRate.Proofs.cover7_leaf0168_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0168_certificate
#check SmaleRate.Proofs.cover7_leaf0169_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0169_certificate
#check SmaleRate.Proofs.cover7_leaf0170_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0170_certificate
#check SmaleRate.Proofs.cover7_leaf0171_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0171_certificate
#check SmaleRate.Proofs.cover7_leaf0172_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0172_certificate
#check SmaleRate.Proofs.cover7_leaf0173_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0173_certificate
#check SmaleRate.Proofs.cover7_leaf0174_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0174_certificate
