/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0975; no trusted numerical premise.
theorem cover8_leaf0975_exp_radius : (998003808933372941/1000000000000000000 : ℝ) ≤ Real.exp ((-8381/524288 : ℝ)/8) ∧ Real.exp ((-8381/524288 : ℝ)/8) ≤ (499001904466686471/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8381/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0975_exp_lower : (460056731157515929/500000000000000000 : ℝ) ≤ Real.exp ((-17051297370133/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051297370133/25600000000000 : ℝ)/8) ≤ (920113462315031859/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051297370133/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0975_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901793179/1000000000000 : ℝ) ≤ 4*Real.exp (67047/524288 : ℝ)*Real.exp (-mu (radius 8 (8381/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901793179/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8381/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0975_exp_radius
  have hrNumeric : (984141600937/1000000000000 : ℝ) ≤ Real.exp (-8381/524288 : ℝ) ∧ Real.exp (-8381/524288 : ℝ) ≤ (492070800469/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984141600937/1000000000000 : ℝ) ≤ (radius 8 (8381/65536 : ℝ)) ∧ (radius 8 (8381/65536 : ℝ)) ≤ (492070800469/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8381/65536 : ℝ)) (984141600937/1000000000000 : ℝ) (492070800469/500000000000 : ℝ) (44346159151/250000000000 : ℝ) (17738463661/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8381/65536 : ℝ)) (984141600937/1000000000000 : ℝ) (492070800469/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8381/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984141600937/1000000000000 : ℝ) (492070800469/500000000000 : ℝ) (248017700117/250000000000 : ℝ) (992070800469/1000000000000 : ℝ) (248009778151/250000000000 : ℝ) (198407822521/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8381/65536 : ℝ)) 1 (248017700117/250000000000 : ℝ) (992070800469/1000000000000 : ℝ) (248009778151/250000000000 : ℝ) (198407822521/200000000000 : ℝ) (124006869567/125000000000 : ℝ) (992054956537/1000000000000 : ℝ) (992054956409/1000000000000 : ℝ) (992054956411/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8381/65536 : ℝ)) 2 (124006869567/125000000000 : ℝ) (992054956537/1000000000000 : ℝ) (992054956409/1000000000000 : ℝ) (992054956411/1000000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8381/65536 : ℝ)) 3 (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8381/65536 : ℝ)) 4 (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8381/65536 : ℝ)) 5 (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8381/65536 : ℝ)) 6 (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8381/65536 : ℝ)) 7 (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8381/65536 : ℝ))) (44346159151/250000000000 : ℝ) (17738463661/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8381/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44346159151/250000000000 : ℝ) (17738463661/100000000000 : ℝ) (294346159151/500000000000 : ℝ) (117738463661/200000000000 : ℝ) (421170555243/1000000000000 : ℝ) (421170555251/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8381/65536 : ℝ))) 1 (294346159151/500000000000 : ℝ) (117738463661/200000000000 : ℝ) (421170555243/1000000000000 : ℝ) (421170555251/1000000000000 : ℝ) (126232859193/250000000000 : ℝ) (252465718389/500000000000 : ℝ) (99587121771/200000000000 : ℝ) (248967804431/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8381/65536 : ℝ))) 2 (126232859193/250000000000 : ℝ) (252465718389/500000000000 : ℝ) (99587121771/200000000000 : ℝ) (248967804431/500000000000 : ℝ) (501433522813/1000000000000 : ℝ) (25071676141/50000000000 : ℝ) (250710661121/500000000000 : ℝ) (501421322249/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8381/65536 : ℝ))) 3 (501433522813/1000000000000 : ℝ) (25071676141/50000000000 : ℝ) (250710661121/500000000000 : ℝ) (501421322249/1000000000000 : ℝ) (501427422527/1000000000000 : ℝ) (100285484507/200000000000 : ℝ) (50142742249/100000000000 : ℝ) (250713711249/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8381/65536 : ℝ))) 4 (501427422527/1000000000000 : ℝ) (100285484507/200000000000 : ℝ) (50142742249/100000000000 : ℝ) (250713711249/500000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8381/65536 : ℝ))) 5 (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8381/65536 : ℝ))) 6 (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8381/65536 : ℝ))) 7 (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8381/65536 : ℝ)) hmem 8 (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8381/65536 : ℝ))) hcmem 8 (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8381/65536 : ℝ)) (124006869559/125000000000 : ℝ) (496027478237/500000000000 : ℝ) (125356855627/250000000000 : ℝ) (501427422517/1000000000000 : ℝ) (99243538411/125000000000 : ℝ) (158789661461/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0975_exp_lower
  have heNumeric : (2054901793179/1000000000000 : ℝ)/4 ≤ Real.exp (-17051297370133/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901793179/1000000000000 : ℝ)/4 ≤ Real.exp ((67047/524288 : ℝ)-(158789661461/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67047/524288 : ℝ) (8381/65536 : ℝ) (158789661461/200000000000 : ℝ) (2054901793179/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0976; no trusted numerical premise.
theorem cover8_leaf0976_exp_radius : (499001889595271063/500000000000000000 : ℝ) ≤ Real.exp ((-67049/4194304 : ℝ)/8) ∧ Real.exp ((-67049/4194304 : ℝ)/8) ≤ (998003779190542127/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67049/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0976_exp_lower : (230028365642781553/250000000000000000 : ℝ) ≤ Real.exp ((-10657060820707/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657060820707/16000000000000 : ℝ)/8) ≤ (920113462571126213/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657060820707/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0976_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450898877/500000000000 : ℝ) ≤ 4*Real.exp (8381/65536 : ℝ)*Real.exp (-mu (radius 8 (67049/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450898877/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67049/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0976_exp_radius
  have hrNumeric : (984141366299/1000000000000 : ℝ) ≤ Real.exp (-67049/4194304 : ℝ) ∧ Real.exp (-67049/4194304 : ℝ) ≤ (9841413663/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984141366299/1000000000000 : ℝ) ≤ (radius 8 (67049/524288 : ℝ)) ∧ (radius 8 (67049/524288 : ℝ)) ≤ (9841413663/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67049/524288 : ℝ)) (984141366299/1000000000000 : ℝ) (9841413663/10000000000 : ℝ) (88692969193/500000000000 : ℝ) (22173242299/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67049/524288 : ℝ)) (984141366299/1000000000000 : ℝ) (9841413663/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67049/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984141366299/1000000000000 : ℝ) (9841413663/10000000000 : ℝ) (992070683149/1000000000000 : ℝ) (19841413663/20000000000 : ℝ) (992038994343/1000000000000 : ℝ) (198407798869/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67049/524288 : ℝ)) 1 (992070683149/1000000000000 : ℝ) (19841413663/20000000000 : ℝ) (992038994343/1000000000000 : ℝ) (198407798869/200000000000 : ℝ) (496027419373/500000000000 : ℝ) (248013709687/250000000000 : ℝ) (992054838619/1000000000000 : ℝ) (992054838621/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67049/524288 : ℝ)) 2 (496027419373/500000000000 : ℝ) (248013709687/250000000000 : ℝ) (992054838619/1000000000000 : ℝ) (992054838621/1000000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67049/524288 : ℝ)) 3 (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67049/524288 : ℝ)) 4 (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67049/524288 : ℝ)) 5 (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67049/524288 : ℝ)) 6 (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67049/524288 : ℝ)) 7 (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67049/524288 : ℝ))) (88692969193/500000000000 : ℝ) (22173242299/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67049/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88692969193/500000000000 : ℝ) (22173242299/125000000000 : ℝ) (588692969193/1000000000000 : ℝ) (147173242299/250000000000 : ℝ) (421172100673/1000000000000 : ℝ) (421172100681/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67049/524288 : ℝ))) 1 (588692969193/1000000000000 : ℝ) (147173242299/250000000000 : ℝ) (421172100673/1000000000000 : ℝ) (421172100681/1000000000000 : ℝ) (504932534933/1000000000000 : ℝ) (504932534939/1000000000000 : ℝ) (248968398841/500000000000 : ℝ) (497936797689/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67049/524288 : ℝ))) 2 (504932534933/1000000000000 : ℝ) (504932534939/1000000000000 : ℝ) (248968398841/500000000000 : ℝ) (497936797689/1000000000000 : ℝ) (501434666307/1000000000000 : ℝ) (250717333157/500000000000 : ℝ) (3133890413/6250000000 : ℝ) (501422466087/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67049/524288 : ℝ))) 3 (501434666307/1000000000000 : ℝ) (250717333157/500000000000 : ℝ) (3133890413/6250000000 : ℝ) (501422466087/1000000000000 : ℝ) (501428566193/1000000000000 : ℝ) (501428566201/1000000000000 : ℝ) (125357141539/250000000000 : ℝ) (125357141541/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67049/524288 : ℝ))) 4 (501428566193/1000000000000 : ℝ) (501428566201/1000000000000 : ℝ) (125357141539/250000000000 : ℝ) (125357141541/250000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67049/524288 : ℝ))) 5 (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67049/524288 : ℝ))) 6 (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67049/524288 : ℝ))) 7 (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67049/524288 : ℝ)) hmem 8 (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67049/524288 : ℝ))) hcmem 8 (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67049/524288 : ℝ)) (496027419341/500000000000 : ℝ) (198410967737/200000000000 : ℝ) (250714283087/500000000000 : ℝ) (501428566183/1000000000000 : ℝ) (793950212409/1000000000000 : ℝ) (793950212427/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0976_exp_lower
  have heNumeric : (1027450898877/500000000000 : ℝ)/4 ≤ Real.exp (-10657060820707/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450898877/500000000000 : ℝ)/4 ≤ Real.exp ((8381/65536 : ℝ)-(793950212427/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8381/65536 : ℝ) (67049/524288 : ℝ) (793950212427/1000000000000 : ℝ) (1027450898877/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0977; no trusted numerical premise.
theorem cover8_leaf0977_exp_radius : (499001874723856099/500000000000000000 : ℝ) ≤ Real.exp ((-33525/2097152 : ℝ)/8) ∧ Real.exp ((-33525/2097152 : ℝ)/8) ≤ (998003749447712199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33525/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0977_exp_lower : (460056731414472889/500000000000000000 : ℝ) ≤ Real.exp ((-85256486278727/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256486278727/128000000000000 : ℝ)/8) ≤ (920113462828945779/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256486278727/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0977_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901802361/1000000000000 : ℝ) ≤ 4*Real.exp (67049/524288 : ℝ)*Real.exp (-mu (radius 8 (33525/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901802361/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33525/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0977_exp_radius
  have hrNumeric : (984141131661/1000000000000 : ℝ) ≤ Real.exp (-33525/2097152 : ℝ) ∧ Real.exp (-33525/2097152 : ℝ) ≤ (492070565831/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984141131661/1000000000000 : ℝ) ≤ (radius 8 (33525/262144 : ℝ)) ∧ (radius 8 (33525/262144 : ℝ)) ≤ (492070565831/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33525/262144 : ℝ)) (984141131661/1000000000000 : ℝ) (492070565831/500000000000 : ℝ) (88693620079/500000000000 : ℝ) (35477448033/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33525/262144 : ℝ)) (984141131661/1000000000000 : ℝ) (492070565831/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33525/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984141131661/1000000000000 : ℝ) (492070565831/500000000000 : ℝ) (99207056583/100000000000 : ℝ) (992070565831/1000000000000 : ℝ) (992038876083/1000000000000 : ℝ) (248009719021/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33525/262144 : ℝ)) 1 (99207056583/100000000000 : ℝ) (992070565831/1000000000000 : ℝ) (992038876083/1000000000000 : ℝ) (248009719021/250000000000 : ℝ) (248013680239/250000000000 : ℝ) (496027360479/500000000000 : ℝ) (992054720829/1000000000000 : ℝ) (992054720831/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33525/262144 : ℝ)) 2 (248013680239/250000000000 : ℝ) (496027360479/500000000000 : ℝ) (992054720829/1000000000000 : ℝ) (992054720831/1000000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33525/262144 : ℝ)) 3 (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33525/262144 : ℝ)) 4 (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33525/262144 : ℝ)) 5 (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33525/262144 : ℝ)) 6 (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33525/262144 : ℝ)) 7 (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33525/262144 : ℝ))) (88693620079/500000000000 : ℝ) (35477448033/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33525/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88693620079/500000000000 : ℝ) (35477448033/200000000000 : ℝ) (588693620079/1000000000000 : ℝ) (588693620083/1000000000000 : ℝ) (210586823043/500000000000 : ℝ) (26323352881/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33525/262144 : ℝ))) 1 (588693620079/1000000000000 : ℝ) (588693620083/1000000000000 : ℝ) (210586823043/500000000000 : ℝ) (26323352881/62500000000 : ℝ) (252466816541/500000000000 : ℝ) (50493363309/100000000000 : ℝ) (7780281039/15625000000 : ℝ) (99587597301/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33525/262144 : ℝ))) 2 (252466816541/500000000000 : ℝ) (50493363309/100000000000 : ℝ) (7780281039/15625000000 : ℝ) (99587597301/200000000000 : ℝ) (501435809789/1000000000000 : ℝ) (250717904899/500000000000 : ℝ) (100284721981/200000000000 : ℝ) (100284721983/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33525/262144 : ℝ))) 3 (501435809789/1000000000000 : ℝ) (250717904899/500000000000 : ℝ) (100284721981/200000000000 : ℝ) (100284721983/200000000000 : ℝ) (501429709847/1000000000000 : ℝ) (501429709857/1000000000000 : ℝ) (501429709809/1000000000000 : ℝ) (25071485491/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33525/262144 : ℝ))) 4 (501429709847/1000000000000 : ℝ) (501429709857/1000000000000 : ℝ) (501429709809/1000000000000 : ℝ) (25071485491/50000000000 : ℝ) (125357427457/250000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33525/262144 : ℝ))) 5 (125357427457/250000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33525/262144 : ℝ))) 6 (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33525/262144 : ℝ))) 7 (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33525/262144 : ℝ)) hmem 8 (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33525/262144 : ℝ))) hcmem 8 (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33525/262144 : ℝ)) (248013680223/250000000000 : ℝ) (198410944179/200000000000 : ℝ) (501429709827/1000000000000 : ℝ) (501429709839/1000000000000 : ℝ) (793952117511/1000000000000 : ℝ) (396976058767/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0977_exp_lower
  have heNumeric : (2054901802361/1000000000000 : ℝ)/4 ≤ Real.exp (-85256486278727/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901802361/1000000000000 : ℝ)/4 ≤ Real.exp ((67049/524288 : ℝ)-(396976058767/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67049/524288 : ℝ) (33525/262144 : ℝ) (396976058767/500000000000 : ℝ) (2054901802361/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0978; no trusted numerical premise.
theorem cover8_leaf0978_exp_radius : (249500929926220789/250000000000000000 : ℝ) ≤ Real.exp ((-67051/4194304 : ℝ)/8) ∧ Real.exp ((-67051/4194304 : ℝ)/8) ≤ (998003719704883157/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67051/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0978_exp_lower : (230028365772640203/250000000000000000 : ℝ) ≤ Real.exp ((-42628242993787/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628242993787/64000000000000 : ℝ)/8) ≤ (920113463090560813/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628242993787/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0978_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980361407/200000000000 : ℝ) ≤ 4*Real.exp (33525/262144 : ℝ)*Real.exp (-mu (radius 8 (67051/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980361407/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67051/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0978_exp_radius
  have hrNumeric : (3844300379/3906250000 : ℝ) ≤ Real.exp (-67051/4194304 : ℝ) ∧ Real.exp (-67051/4194304 : ℝ) ≤ (39365635881/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (3844300379/3906250000 : ℝ) ≤ (radius 8 (67051/524288 : ℝ)) ∧ (radius 8 (67051/524288 : ℝ)) ≤ (39365635881/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67051/524288 : ℝ)) (3844300379/3906250000 : ℝ) (39365635881/40000000000 : ℝ) (35477708383/200000000000 : ℝ) (177388541921/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67051/524288 : ℝ)) (3844300379/3906250000 : ℝ) (39365635881/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67051/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (3844300379/3906250000 : ℝ) (39365635881/40000000000 : ℝ) (7750550379/7812500000 : ℝ) (992070448513/1000000000000 : ℝ) (992038757823/1000000000000 : ℝ) (39681550313/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67051/524288 : ℝ)) 1 (7750550379/7812500000 : ℝ) (992070448513/1000000000000 : ℝ) (992038757823/1000000000000 : ℝ) (39681550313/40000000000 : ℝ) (992054603167/1000000000000 : ℝ) (992054603169/1000000000000 : ℝ) (6200341269/6250000000 : ℝ) (992054603043/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67051/524288 : ℝ)) 2 (992054603167/1000000000000 : ℝ) (992054603169/1000000000000 : ℝ) (6200341269/6250000000 : ℝ) (992054603043/1000000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67051/524288 : ℝ)) 3 (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67051/524288 : ℝ)) 4 (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67051/524288 : ℝ)) 5 (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67051/524288 : ℝ)) 6 (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67051/524288 : ℝ)) 7 (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67051/524288 : ℝ))) (35477708383/200000000000 : ℝ) (177388541921/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67051/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35477708383/200000000000 : ℝ) (177388541921/1000000000000 : ℝ) (588694270957/1000000000000 : ℝ) (588694270961/1000000000000 : ℝ) (105293797869/250000000000 : ℝ) (105293797871/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67051/524288 : ℝ))) 1 (588694270957/1000000000000 : ℝ) (588694270961/1000000000000 : ℝ) (105293797869/250000000000 : ℝ) (105293797871/250000000000 : ℝ) (31558420701/62500000000 : ℝ) (504934731223/1000000000000 : ℝ) (124484793823/250000000000 : ℝ) (4979391753/10000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67051/524288 : ℝ))) 2 (31558420701/62500000000 : ℝ) (504934731223/1000000000000 : ℝ) (124484793823/250000000000 : ℝ) (4979391753/10000000000 : ℝ) (250718476627/500000000000 : ℝ) (250718476631/500000000000 : ℝ) (250712376857/500000000000 : ℝ) (501424753723/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67051/524288 : ℝ))) 3 (250718476627/500000000000 : ℝ) (250718476631/500000000000 : ℝ) (250712376857/500000000000 : ℝ) (501424753723/1000000000000 : ℝ) (125357713371/250000000000 : ℝ) (501430853493/1000000000000 : ℝ) (250715426723/500000000000 : ℝ) (31339428341/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67051/524288 : ℝ))) 4 (125357713371/250000000000 : ℝ) (501430853493/1000000000000 : ℝ) (250715426723/500000000000 : ℝ) (31339428341/62500000000 : ℝ) (100286170693/200000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67051/524288 : ℝ))) 5 (100286170693/200000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67051/524288 : ℝ))) 6 (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67051/524288 : ℝ))) 7 (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67051/524288 : ℝ)) hmem 8 (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67051/524288 : ℝ))) hcmem 8 (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67051/524288 : ℝ)) (992054603103/1000000000000 : ℝ) (496027301553/500000000000 : ℝ) (62678856683/125000000000 : ℝ) (20057234139/40000000000 : ℝ) (793954022587/1000000000000 : ℝ) (49622126413/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0978_exp_lower
  have heNumeric : (410980361407/200000000000 : ℝ)/4 ≤ Real.exp (-42628242993787/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980361407/200000000000 : ℝ)/4 ≤ Real.exp ((33525/262144 : ℝ)-(49622126413/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33525/262144 : ℝ) (67051/524288 : ℝ) (49622126413/62500000000 : ℝ) (410980361407/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0979; no trusted numerical premise.
theorem cover8_leaf0979_exp_radius : (199600737992411/200000000000000 : ℝ) ≤ Real.exp ((-16763/1048576 : ℝ)/8) ∧ Real.exp ((-16763/1048576 : ℝ)/8) ≤ (998003689962055001/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16763/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0979_exp_lower : (460056731676605487/500000000000000000 : ℝ) ≤ Real.exp ((-85256485695269/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256485695269/128000000000000 : ℝ)/8) ≤ (36804538534128439/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256485695269/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0979_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901811727/1000000000000 : ℝ) ≤ 4*Real.exp (67051/524288 : ℝ)*Real.exp (-mu (radius 8 (16763/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901811727/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16763/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0979_exp_radius
  have hrNumeric : (492070331193/500000000000 : ℝ) ≤ Real.exp (-16763/1048576 : ℝ) ∧ Real.exp (-16763/1048576 : ℝ) ≤ (984140662387/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492070331193/500000000000 : ℝ) ≤ (radius 8 (16763/131072 : ℝ)) ∧ (radius 8 (16763/131072 : ℝ)) ≤ (984140662387/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16763/131072 : ℝ)) (492070331193/500000000000 : ℝ) (984140662387/1000000000000 : ℝ) (177389843667/1000000000000 : ℝ) (88694921837/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16763/131072 : ℝ)) (492070331193/500000000000 : ℝ) (984140662387/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16763/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492070331193/500000000000 : ℝ) (984140662387/1000000000000 : ℝ) (992070331193/1000000000000 : ℝ) (496035165597/500000000000 : ℝ) (496019319781/500000000000 : ℝ) (248009659891/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16763/131072 : ℝ)) 1 (992070331193/1000000000000 : ℝ) (496035165597/500000000000 : ℝ) (496019319781/500000000000 : ℝ) (248009659891/250000000000 : ℝ) (992054485377/1000000000000 : ℝ) (992054485379/1000000000000 : ℝ) (3968217941/4000000000 : ℝ) (992054485253/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16763/131072 : ℝ)) 2 (992054485377/1000000000000 : ℝ) (992054485379/1000000000000 : ℝ) (3968217941/4000000000 : ℝ) (992054485253/1000000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16763/131072 : ℝ)) 3 (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16763/131072 : ℝ)) 4 (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16763/131072 : ℝ)) 5 (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16763/131072 : ℝ)) 6 (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16763/131072 : ℝ)) 7 (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16763/131072 : ℝ))) (177389843667/1000000000000 : ℝ) (88694921837/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16763/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177389843667/1000000000000 : ℝ) (88694921837/500000000000 : ℝ) (588694921833/1000000000000 : ℝ) (588694921837/1000000000000 : ℝ) (210588368427/500000000000 : ℝ) (421176736863/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16763/131072 : ℝ))) 1 (588694921833/1000000000000 : ℝ) (588694921837/1000000000000 : ℝ) (210588368427/500000000000 : ℝ) (421176736863/1000000000000 : ℝ) (504935829343/1000000000000 : ℝ) (10098716587/20000000000 : ℝ) (6224254551/12500000000 : ℝ) (62242545511/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16763/131072 : ℝ))) 2 (504935829343/1000000000000 : ℝ) (10098716587/20000000000 : ℝ) (6224254551/12500000000 : ℝ) (62242545511/125000000000 : ℝ) (501438096711/1000000000000 : ℝ) (501438096719/1000000000000 : ℝ) (125356474379/250000000000 : ℝ) (125356474381/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16763/131072 : ℝ))) 3 (501438096711/1000000000000 : ℝ) (501438096719/1000000000000 : ℝ) (125356474379/250000000000 : ℝ) (125356474381/250000000000 : ℝ) (501431997113/1000000000000 : ℝ) (250715998561/500000000000 : ℝ) (125357999269/250000000000 : ℝ) (100286399417/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16763/131072 : ℝ))) 4 (501431997113/1000000000000 : ℝ) (250715998561/500000000000 : ℝ) (125357999269/250000000000 : ℝ) (100286399417/200000000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16763/131072 : ℝ))) 5 (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16763/131072 : ℝ))) 6 (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16763/131072 : ℝ))) 7 (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16763/131072 : ℝ)) hmem 8 (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16763/131072 : ℝ))) hcmem 8 (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16763/131072 : ℝ)) (992054485313/1000000000000 : ℝ) (248013621329/250000000000 : ℝ) (250715998547/500000000000 : ℝ) (31339499819/62500000000 : ℝ) (396977963827/500000000000 : ℝ) (793955927673/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0979_exp_lower
  have heNumeric : (2054901811727/1000000000000 : ℝ)/4 ≤ Real.exp (-85256485695269/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901811727/1000000000000 : ℝ)/4 ≤ Real.exp ((67051/524288 : ℝ)-(793955927673/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67051/524288 : ℝ) (16763/131072 : ℝ) (793955927673/1000000000000 : ℝ) (2054901811727/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0980; no trusted numerical premise.
theorem cover8_leaf0980_exp_radius : (998003660219227731/1000000000000000000 : ℝ) ≤ Real.exp ((-67053/4194304 : ℝ)/8) ∧ Real.exp ((-67053/4194304 : ℝ)/8) ≤ (249500915054806933/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67053/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0980_exp_lower : (184022692723770301/200000000000000000 : ℝ) ≤ Real.exp ((-21314121349909/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314121349909/32000000000000 : ℝ)/8) ≤ (460056731809425753/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314121349909/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0980_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901816473/1000000000000 : ℝ) ≤ 4*Real.exp (16763/131072 : ℝ)*Real.exp (-mu (radius 8 (67053/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901816473/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67053/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0980_exp_radius
  have hrNumeric : (984140427749/1000000000000 : ℝ) ≤ Real.exp (-67053/4194304 : ℝ) ∧ Real.exp (-67053/4194304 : ℝ) ≤ (3936561711/4000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984140427749/1000000000000 : ℝ) ≤ (radius 8 (67053/524288 : ℝ)) ∧ (radius 8 (67053/524288 : ℝ)) ≤ (3936561711/4000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67053/524288 : ℝ)) (984140427749/1000000000000 : ℝ) (3936561711/4000000000 : ℝ) (44347786351/250000000000 : ℝ) (177391145411/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67053/524288 : ℝ)) (984140427749/1000000000000 : ℝ) (3936561711/4000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67053/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984140427749/1000000000000 : ℝ) (3936561711/4000000000 : ℝ) (496035106937/500000000000 : ℝ) (7936561711/8000000000 : ℝ) (496019260651/500000000000 : ℝ) (124004815163/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67053/524288 : ℝ)) 1 (496035106937/500000000000 : ℝ) (7936561711/8000000000 : ℝ) (496019260651/500000000000 : ℝ) (124004815163/125000000000 : ℝ) (248013591897/250000000000 : ℝ) (99205436759/100000000000 : ℝ) (992054367461/1000000000000 : ℝ) (992054367463/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67053/524288 : ℝ)) 2 (248013591897/250000000000 : ℝ) (99205436759/100000000000 : ℝ) (992054367461/1000000000000 : ℝ) (992054367463/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67053/524288 : ℝ)) 3 (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67053/524288 : ℝ)) 4 (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67053/524288 : ℝ)) 5 (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67053/524288 : ℝ)) 6 (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67053/524288 : ℝ)) 7 (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67053/524288 : ℝ))) (44347786351/250000000000 : ℝ) (177391145411/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67053/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44347786351/250000000000 : ℝ) (177391145411/1000000000000 : ℝ) (294347786351/500000000000 : ℝ) (294347786353/500000000000 : ℝ) (13161821319/31250000000 : ℝ) (421178282217/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67053/524288 : ℝ))) 1 (294347786351/500000000000 : ℝ) (294347786353/500000000000 : ℝ) (13161821319/31250000000 : ℝ) (421178282217/1000000000000 : ℝ) (100987385491/200000000000 : ℝ) (252468463731/500000000000 : ℝ) (497941552849/1000000000000 : ℝ) (497941552857/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67053/524288 : ℝ))) 2 (100987385491/200000000000 : ℝ) (252468463731/500000000000 : ℝ) (497941552849/1000000000000 : ℝ) (497941552857/1000000000000 : ℝ) (62679905019/125000000000 : ℝ) (3133995251/6250000000 : ℝ) (5014270413/10000000000 : ℝ) (501427041309/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67053/524288 : ℝ))) 3 (62679905019/125000000000 : ℝ) (3133995251/6250000000 : ℝ) (5014270413/10000000000 : ℝ) (501427041309/1000000000000 : ℝ) (250716570363/500000000000 : ℝ) (100286628147/200000000000 : ℝ) (31339571293/62500000000 : ℝ) (250716570349/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67053/524288 : ℝ))) 4 (250716570363/500000000000 : ℝ) (100286628147/200000000000 : ℝ) (31339571293/62500000000 : ℝ) (250716570349/500000000000 : ℝ) (501433140707/1000000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67053/524288 : ℝ))) 5 (501433140707/1000000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67053/524288 : ℝ))) 6 (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67053/524288 : ℝ))) 7 (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67053/524288 : ℝ)) hmem 8 (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67053/524288 : ℝ))) hcmem 8 (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67053/524288 : ℝ)) (248013591881/250000000000 : ℝ) (992054367527/1000000000000 : ℝ) (250716570353/500000000000 : ℝ) (501433140717/1000000000000 : ℝ) (793957832691/1000000000000 : ℝ) (99244729089/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0980_exp_lower
  have heNumeric : (2054901816473/1000000000000 : ℝ)/4 ≤ Real.exp (-21314121349909/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901816473/1000000000000 : ℝ)/4 ≤ Real.exp ((16763/131072 : ℝ)-(99244729089/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16763/131072 : ℝ) (67053/524288 : ℝ) (99244729089/125000000000 : ℝ) (2054901816473/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0981; no trusted numerical premise.
theorem cover8_leaf0981_exp_radius : (249500907619100337/250000000000000000 : ℝ) ≤ Real.exp ((-33527/2097152 : ℝ)/8) ∧ Real.exp ((-33527/2097152 : ℝ)/8) ≤ (998003630476401349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33527/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0981_exp_lower : (1437677287323113/1562500000000000 : ℝ) ≤ Real.exp ((-85256485101443/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256485101443/128000000000000 : ℝ)/8) ≤ (920113463886792321/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256485101443/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0981_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901821261/1000000000000 : ℝ) ≤ 4*Real.exp (67053/524288 : ℝ)*Real.exp (-mu (radius 8 (33527/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901821261/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33527/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0981_exp_radius
  have hrNumeric : (123017524139/125000000000 : ℝ) ≤ Real.exp (-33527/2097152 : ℝ) ∧ Real.exp (-33527/2097152 : ℝ) ≤ (984140193113/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123017524139/125000000000 : ℝ) ≤ (radius 8 (33527/262144 : ℝ)) ∧ (radius 8 (33527/262144 : ℝ)) ≤ (984140193113/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33527/262144 : ℝ)) (123017524139/125000000000 : ℝ) (984140193113/1000000000000 : ℝ) (44348111783/250000000000 : ℝ) (88696223569/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33527/262144 : ℝ)) (123017524139/125000000000 : ℝ) (984140193113/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33527/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123017524139/125000000000 : ℝ) (984140193113/1000000000000 : ℝ) (248017524139/250000000000 : ℝ) (992070096557/1000000000000 : ℝ) (496019201521/500000000000 : ℝ) (248009600761/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33527/262144 : ℝ)) 1 (248017524139/250000000000 : ℝ) (992070096557/1000000000000 : ℝ) (496019201521/500000000000 : ℝ) (248009600761/250000000000 : ℝ) (992054249799/1000000000000 : ℝ) (992054249801/1000000000000 : ℝ) (124006781209/125000000000 : ℝ) (496027124837/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33527/262144 : ℝ)) 2 (992054249799/1000000000000 : ℝ) (992054249801/1000000000000 : ℝ) (124006781209/125000000000 : ℝ) (496027124837/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33527/262144 : ℝ)) 3 (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33527/262144 : ℝ)) 4 (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33527/262144 : ℝ)) 5 (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33527/262144 : ℝ)) 6 (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33527/262144 : ℝ)) 7 (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33527/262144 : ℝ))) (44348111783/250000000000 : ℝ) (88696223569/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33527/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44348111783/250000000000 : ℝ) (88696223569/500000000000 : ℝ) (294348111783/500000000000 : ℝ) (588696223569/1000000000000 : ℝ) (210589913773/500000000000 : ℝ) (210589913777/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33527/262144 : ℝ))) 1 (294348111783/500000000000 : ℝ) (588696223569/1000000000000 : ℝ) (210589913773/500000000000 : ℝ) (210589913777/500000000000 : ℝ) (126234506389/250000000000 : ℝ) (252469012781/500000000000 : ℝ) (248971370803/500000000000 : ℝ) (497942741613/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33527/262144 : ℝ))) 2 (126234506389/250000000000 : ℝ) (252469012781/500000000000 : ℝ) (248971370803/500000000000 : ℝ) (497942741613/1000000000000 : ℝ) (501440383581/1000000000000 : ℝ) (125360095897/250000000000 : ℝ) (501428185073/1000000000000 : ℝ) (501428185081/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33527/262144 : ℝ))) 3 (501440383581/1000000000000 : ℝ) (125360095897/250000000000 : ℝ) (501428185073/1000000000000 : ℝ) (501428185081/1000000000000 : ℝ) (501434284327/1000000000000 : ℝ) (100286856867/200000000000 : ℝ) (501434284289/1000000000000 : ℝ) (250717142149/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33527/262144 : ℝ))) 4 (501434284327/1000000000000 : ℝ) (100286856867/200000000000 : ℝ) (501434284289/1000000000000 : ℝ) (250717142149/500000000000 : ℝ) (125358571077/250000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33527/262144 : ℝ))) 5 (125358571077/250000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33527/262144 : ℝ))) 6 (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33527/262144 : ℝ))) 7 (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33527/262144 : ℝ)) hmem 8 (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33527/262144 : ℝ))) hcmem 8 (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33527/262144 : ℝ)) (198410849947/200000000000 : ℝ) (496027124869/500000000000 : ℝ) (501434284307/1000000000000 : ℝ) (501434284317/1000000000000 : ℝ) (49622483607/62500000000 : ℝ) (793959737731/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0981_exp_lower
  have heNumeric : (2054901821261/1000000000000 : ℝ)/4 ≤ Real.exp (-85256485101443/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901821261/1000000000000 : ℝ)/4 ≤ Real.exp ((67053/524288 : ℝ)-(793959737731/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67053/524288 : ℝ) (33527/262144 : ℝ) (793959737731/1000000000000 : ℝ) (2054901821261/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0982; no trusted numerical premise.
theorem cover8_leaf0982_exp_radius : (249500900183393963/250000000000000000 : ℝ) ≤ Real.exp ((-67055/4194304 : ℝ)/8) ∧ Real.exp ((-67055/4194304 : ℝ)/8) ≤ (998003600733575853/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67055/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0982_exp_lower : (230028366038970819/250000000000000000 : ℝ) ≤ Real.exp ((-8525648480197/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525648480197/12800000000000 : ℝ)/8) ≤ (920113464155883277/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525648480197/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0982_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725456517/250000000000 : ℝ) ≤ 4*Real.exp (33527/262144 : ℝ)*Real.exp (-mu (radius 8 (67055/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725456517/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67055/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0982_exp_radius
  have hrNumeric : (492069979237/500000000000 : ℝ) ≤ Real.exp (-67055/4194304 : ℝ) ∧ Real.exp (-67055/4194304 : ℝ) ≤ (39365598339/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492069979237/500000000000 : ℝ) ≤ (radius 8 (67055/524288 : ℝ)) ∧ (radius 8 (67055/524288 : ℝ)) ≤ (39365598339/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67055/524288 : ℝ)) (492069979237/500000000000 : ℝ) (39365598339/40000000000 : ℝ) (88696874427/500000000000 : ℝ) (177393748861/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67055/524288 : ℝ)) (492069979237/500000000000 : ℝ) (39365598339/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67055/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492069979237/500000000000 : ℝ) (39365598339/40000000000 : ℝ) (992069979237/1000000000000 : ℝ) (496034989619/500000000000 : ℝ) (496019142391/500000000000 : ℝ) (992038284783/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67055/524288 : ℝ)) 1 (992069979237/1000000000000 : ℝ) (496034989619/500000000000 : ℝ) (496019142391/500000000000 : ℝ) (992038284783/1000000000000 : ℝ) (992054132009/1000000000000 : ℝ) (992054132011/1000000000000 : ℝ) (496027065941/500000000000 : ℝ) (248013532971/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67055/524288 : ℝ)) 2 (992054132009/1000000000000 : ℝ) (992054132011/1000000000000 : ℝ) (496027065941/500000000000 : ℝ) (248013532971/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67055/524288 : ℝ)) 3 (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67055/524288 : ℝ)) 4 (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67055/524288 : ℝ)) 5 (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67055/524288 : ℝ)) 6 (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67055/524288 : ℝ)) 7 (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67055/524288 : ℝ))) (88696874427/500000000000 : ℝ) (177393748861/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67055/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88696874427/500000000000 : ℝ) (177393748861/1000000000000 : ℝ) (588696874427/1000000000000 : ℝ) (588696874431/1000000000000 : ℝ) (421181372871/1000000000000 : ℝ) (5264767161/12500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67055/524288 : ℝ))) 1 (588696874427/1000000000000 : ℝ) (588696874431/1000000000000 : ℝ) (421181372871/1000000000000 : ℝ) (5264767161/12500000000 : ℝ) (504939123649/1000000000000 : ℝ) (63117390457/125000000000 : ℝ) (497943930353/1000000000000 : ℝ) (497943930361/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67055/524288 : ℝ))) 2 (504939123649/1000000000000 : ℝ) (63117390457/125000000000 : ℝ) (497943930353/1000000000000 : ℝ) (497943930361/1000000000000 : ℝ) (501441527001/1000000000000 : ℝ) (501441527009/1000000000000 : ℝ) (501429328837/1000000000000 : ℝ) (250714664423/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67055/524288 : ℝ))) 3 (501441527001/1000000000000 : ℝ) (501441527009/1000000000000 : ℝ) (501429328837/1000000000000 : ℝ) (250714664423/500000000000 : ℝ) (501435427919/1000000000000 : ℝ) (62679428491/125000000000 : ℝ) (501435427881/1000000000000 : ℝ) (501435427891/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67055/524288 : ℝ))) 4 (501435427919/1000000000000 : ℝ) (62679428491/125000000000 : ℝ) (501435427881/1000000000000 : ℝ) (501435427891/1000000000000 : ℝ) (5014354279/10000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67055/524288 : ℝ))) 5 (5014354279/10000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67055/524288 : ℝ))) 6 (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67055/524288 : ℝ))) 7 (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67055/524288 : ℝ)) hmem 8 (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67055/524288 : ℝ))) hcmem 8 (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67055/524288 : ℝ)) (198410826389/200000000000 : ℝ) (248013532987/250000000000 : ℝ) (501435427899/1000000000000 : ℝ) (50143542791/100000000000 : ℝ) (793961642719/1000000000000 : ℝ) (39698082137/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0982_exp_lower
  have heNumeric : (513725456517/250000000000 : ℝ)/4 ≤ Real.exp (-8525648480197/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725456517/250000000000 : ℝ)/4 ≤ Real.exp ((33527/262144 : ℝ)-(39698082137/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33527/262144 : ℝ) (67055/524288 : ℝ) (39698082137/50000000000 : ℝ) (513725456517/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0983; no trusted numerical premise.
theorem cover8_leaf0983_exp_radius : (499001785495375621/500000000000000000 : ℝ) ≤ Real.exp ((-4191/262144 : ℝ)/8) ∧ Real.exp ((-4191/262144 : ℝ)/8) ≤ (998003570990751243/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4191/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0983_exp_lower : (184022692885615923/200000000000000000 : ℝ) ≤ Real.exp ((-85256484499041/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256484499041/128000000000000 : ℝ)/8) ≤ (1797096610211093/1953125000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256484499041/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0983_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725457733/250000000000 : ℝ) ≤ 4*Real.exp (67055/524288 : ℝ)*Real.exp (-mu (radius 8 (4191/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513725457733/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4191/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0983_exp_radius
  have hrNumeric : (984139723837/1000000000000 : ℝ) ≤ Real.exp (-4191/262144 : ℝ) ∧ Real.exp (-4191/262144 : ℝ) ≤ (492069861919/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984139723837/1000000000000 : ℝ) ≤ (radius 8 (4191/32768 : ℝ)) ∧ (radius 8 (4191/32768 : ℝ)) ≤ (492069861919/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4191/32768 : ℝ)) (984139723837/1000000000000 : ℝ) (492069861919/500000000000 : ℝ) (88697525281/500000000000 : ℝ) (177395050569/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4191/32768 : ℝ)) (984139723837/1000000000000 : ℝ) (492069861919/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4191/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984139723837/1000000000000 : ℝ) (492069861919/500000000000 : ℝ) (496034930959/500000000000 : ℝ) (992069861919/1000000000000 : ℝ) (496019083261/500000000000 : ℝ) (992038166523/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4191/32768 : ℝ)) 1 (496034930959/500000000000 : ℝ) (992069861919/1000000000000 : ℝ) (496019083261/500000000000 : ℝ) (992038166523/1000000000000 : ℝ) (49602700711/50000000000 : ℝ) (992054014221/1000000000000 : ℝ) (992054014093/1000000000000 : ℝ) (198410802819/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4191/32768 : ℝ)) 2 (49602700711/50000000000 : ℝ) (992054014221/1000000000000 : ℝ) (992054014093/1000000000000 : ℝ) (198410802819/200000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4191/32768 : ℝ)) 3 (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4191/32768 : ℝ)) 4 (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4191/32768 : ℝ)) 5 (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4191/32768 : ℝ)) 6 (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4191/32768 : ℝ)) 7 (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4191/32768 : ℝ))) (88697525281/500000000000 : ℝ) (177395050569/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4191/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88697525281/500000000000 : ℝ) (177395050569/1000000000000 : ℝ) (588697525281/1000000000000 : ℝ) (117739505057/200000000000 : ℝ) (210591459087/500000000000 : ℝ) (421182918183/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4191/32768 : ℝ))) 1 (588697525281/1000000000000 : ℝ) (117739505057/200000000000 : ℝ) (210591459087/500000000000 : ℝ) (421182918183/1000000000000 : ℝ) (504940221727/1000000000000 : ℝ) (252470110867/500000000000 : ℝ) (124486279771/250000000000 : ℝ) (124486279773/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4191/32768 : ℝ))) 2 (504940221727/1000000000000 : ℝ) (252470110867/500000000000 : ℝ) (124486279771/250000000000 : ℝ) (124486279773/250000000000 : ℝ) (100288534081/200000000000 : ℝ) (501442670413/1000000000000 : ℝ) (250715236293/500000000000 : ℝ) (250715236297/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4191/32768 : ℝ))) 3 (100288534081/200000000000 : ℝ) (501442670413/1000000000000 : ℝ) (250715236293/500000000000 : ℝ) (250715236297/500000000000 : ℝ) (100287314299/200000000000 : ℝ) (31339785719/62500000000 : ℝ) (250718285729/500000000000 : ℝ) (501436571467/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4191/32768 : ℝ))) 4 (100287314299/200000000000 : ℝ) (31339785719/62500000000 : ℝ) (250718285729/500000000000 : ℝ) (501436571467/1000000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4191/32768 : ℝ))) 5 (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4191/32768 : ℝ))) 6 (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4191/32768 : ℝ))) 7 (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4191/32768 : ℝ)) hmem 8 (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4191/32768 : ℝ))) hcmem 8 (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4191/32768 : ℝ)) (248013503539/250000000000 : ℝ) (496027007079/500000000000 : ℝ) (125359142869/250000000000 : ℝ) (250718285743/500000000000 : ℝ) (99245443463/125000000000 : ℝ) (396981773861/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0983_exp_lower
  have heNumeric : (513725457733/250000000000 : ℝ)/4 ≤ Real.exp (-85256484499041/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725457733/250000000000 : ℝ)/4 ≤ Real.exp ((67055/524288 : ℝ)-(396981773861/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67055/524288 : ℝ) (4191/32768 : ℝ) (396981773861/500000000000 : ℝ) (513725457733/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0984; no trusted numerical premise.
theorem cover8_leaf0984_exp_radius : (998003541247927519/1000000000000000000 : ℝ) ≤ Real.exp ((-67057/4194304 : ℝ)/8) ∧ Real.exp ((-67057/4194304 : ℝ)/8) ≤ (6237522132799547/6250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67057/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0984_exp_lower : (92011346470234621/100000000000000000 : ℝ) ≤ Real.exp ((-5328530262113/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328530262113/8000000000000 : ℝ)/8) ≤ (920113464702346211/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328530262113/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0984_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862729479/125000000000 : ℝ) ≤ 4*Real.exp (4191/32768 : ℝ)*Real.exp (-mu (radius 8 (67057/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862729479/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67057/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0984_exp_radius
  have hrNumeric : (2460348723/2500000000 : ℝ) ≤ Real.exp (-67057/4194304 : ℝ) ∧ Real.exp (-67057/4194304 : ℝ) ≤ (984139489201/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (2460348723/2500000000 : ℝ) ≤ (radius 8 (67057/524288 : ℝ)) ∧ (radius 8 (67057/524288 : ℝ)) ≤ (984139489201/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67057/524288 : ℝ)) (2460348723/2500000000 : ℝ) (984139489201/1000000000000 : ℝ) (8869817613/50000000000 : ℝ) (88698176133/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67057/524288 : ℝ)) (2460348723/2500000000 : ℝ) (984139489201/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67057/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (2460348723/2500000000 : ℝ) (984139489201/1000000000000 : ℝ) (4960348723/5000000000 : ℝ) (992069744601/1000000000000 : ℝ) (496019024131/500000000000 : ℝ) (992038048263/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67057/524288 : ℝ)) 1 (4960348723/5000000000 : ℝ) (992069744601/1000000000000 : ℝ) (496019024131/500000000000 : ℝ) (992038048263/1000000000000 : ℝ) (992053896431/1000000000000 : ℝ) (62003368527/62500000000 : ℝ) (62003368519/62500000000 : ℝ) (496026948153/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67057/524288 : ℝ)) 2 (992053896431/1000000000000 : ℝ) (62003368527/62500000000 : ℝ) (62003368519/62500000000 : ℝ) (496026948153/500000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67057/524288 : ℝ)) 3 (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67057/524288 : ℝ)) 4 (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67057/524288 : ℝ)) 5 (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67057/524288 : ℝ)) 6 (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67057/524288 : ℝ)) 7 (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67057/524288 : ℝ))) (8869817613/50000000000 : ℝ) (88698176133/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67057/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8869817613/50000000000 : ℝ) (88698176133/500000000000 : ℝ) (58869817613/100000000000 : ℝ) (588698176133/1000000000000 : ℝ) (421184463459/1000000000000 : ℝ) (105296115867/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67057/524288 : ℝ))) 1 (58869817613/100000000000 : ℝ) (588698176133/1000000000000 : ℝ) (421184463459/1000000000000 : ℝ) (105296115867/250000000000 : ℝ) (252470659897/500000000000 : ℝ) (504941319801/1000000000000 : ℝ) (2489731539/5000000000 : ℝ) (15560822119/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67057/524288 : ℝ))) 2 (252470659897/500000000000 : ℝ) (504941319801/1000000000000 : ℝ) (2489731539/5000000000 : ℝ) (15560822119/31250000000 : ℝ) (501443813797/1000000000000 : ℝ) (100288762761/200000000000 : ℝ) (501431616321/1000000000000 : ℝ) (50143161633/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67057/524288 : ℝ))) 3 (501443813797/1000000000000 : ℝ) (100288762761/200000000000 : ℝ) (501431616321/1000000000000 : ℝ) (50143161633/100000000000 : ℝ) (501437715059/1000000000000 : ℝ) (125359428767/250000000000 : ℝ) (501437715021/1000000000000 : ℝ) (501437715031/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67057/524288 : ℝ))) 4 (501437715059/1000000000000 : ℝ) (125359428767/250000000000 : ℝ) (501437715021/1000000000000 : ℝ) (501437715031/1000000000000 : ℝ) (3133985719/6250000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67057/524288 : ℝ))) 5 (3133985719/6250000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67057/524288 : ℝ))) 6 (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67057/524288 : ℝ))) 7 (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67057/524288 : ℝ)) hmem 8 (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67057/524288 : ℝ))) hcmem 8 (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67057/524288 : ℝ)) (992053896367/1000000000000 : ℝ) (992053896369/1000000000000 : ℝ) (501437715039/1000000000000 : ℝ) (10028754301/20000000000 : ℝ) (396982726333/500000000000 : ℝ) (396982726343/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0984_exp_lower
  have heNumeric : (256862729479/125000000000 : ℝ)/4 ≤ Real.exp (-5328530262113/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862729479/125000000000 : ℝ)/4 ≤ Real.exp ((4191/32768 : ℝ)-(396982726343/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4191/32768 : ℝ) (67057/524288 : ℝ) (396982726343/500000000000 : ℝ) (256862729479/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0985; no trusted numerical premise.
theorem cover8_leaf0985_exp_radius : (499001755752552341/500000000000000000 : ℝ) ≤ Real.exp ((-33529/2097152 : ℝ)/8) ∧ Real.exp ((-33529/2097152 : ℝ)/8) ≤ (998003511505104683/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33529/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0985_exp_lower : (920113464978913089/1000000000000000000 : ℝ) ≤ Real.exp ((-17051296777203/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051296777203/25600000000000 : ℝ)/8) ≤ (92011346497891309/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051296777203/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0985_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901840773/1000000000000 : ℝ) ≤ 4*Real.exp (67057/524288 : ℝ)*Real.exp (-mu (radius 8 (33529/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901840773/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33529/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0985_exp_radius
  have hrNumeric : (984139254563/1000000000000 : ℝ) ≤ Real.exp (-33529/2097152 : ℝ) ∧ Real.exp (-33529/2097152 : ℝ) ≤ (246034813641/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984139254563/1000000000000 : ℝ) ≤ (radius 8 (33529/262144 : ℝ)) ∧ (radius 8 (33529/262144 : ℝ)) ≤ (246034813641/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33529/262144 : ℝ)) (984139254563/1000000000000 : ℝ) (246034813641/250000000000 : ℝ) (177397653947/1000000000000 : ℝ) (88698826977/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33529/262144 : ℝ)) (984139254563/1000000000000 : ℝ) (246034813641/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33529/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984139254563/1000000000000 : ℝ) (246034813641/250000000000 : ℝ) (992069627281/1000000000000 : ℝ) (496034813641/500000000000 : ℝ) (496018965001/500000000000 : ℝ) (992037930003/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33529/262144 : ℝ)) 1 (992069627281/1000000000000 : ℝ) (496034813641/500000000000 : ℝ) (496018965001/500000000000 : ℝ) (992037930003/1000000000000 : ℝ) (992053778641/1000000000000 : ℝ) (992053778643/1000000000000 : ℝ) (496026889257/500000000000 : ℝ) (248013444629/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33529/262144 : ℝ)) 2 (992053778641/1000000000000 : ℝ) (992053778643/1000000000000 : ℝ) (496026889257/500000000000 : ℝ) (248013444629/250000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33529/262144 : ℝ)) 3 (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33529/262144 : ℝ)) 4 (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33529/262144 : ℝ)) 5 (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33529/262144 : ℝ)) 6 (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33529/262144 : ℝ)) 7 (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33529/262144 : ℝ))) (177397653947/1000000000000 : ℝ) (88698826977/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33529/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177397653947/1000000000000 : ℝ) (88698826977/500000000000 : ℝ) (588698826973/1000000000000 : ℝ) (588698826977/1000000000000 : ℝ) (210593004363/500000000000 : ℝ) (84237201747/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33529/262144 : ℝ))) 1 (588698826973/1000000000000 : ℝ) (588698826977/1000000000000 : ℝ) (210593004363/500000000000 : ℝ) (84237201747/200000000000 : ℝ) (504942417849/1000000000000 : ℝ) (7889725279/15625000000 : ℝ) (497947496503/1000000000000 : ℝ) (497947496511/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33529/262144 : ℝ))) 2 (504942417849/1000000000000 : ℝ) (7889725279/15625000000 : ℝ) (497947496503/1000000000000 : ℝ) (497947496511/1000000000000 : ℝ) (62680619647/125000000000 : ℝ) (489692341/976562500 : ℝ) (125358190011/250000000000 : ℝ) (501432760053/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33529/262144 : ℝ))) 3 (62680619647/125000000000 : ℝ) (489692341/976562500 : ℝ) (125358190011/250000000000 : ℝ) (501432760053/1000000000000 : ℝ) (50143885861/100000000000 : ℝ) (501438858619/1000000000000 : ℝ) (125359714643/250000000000 : ℝ) (250719429291/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33529/262144 : ℝ))) 4 (50143885861/100000000000 : ℝ) (501438858619/1000000000000 : ℝ) (125359714643/250000000000 : ℝ) (250719429291/500000000000 : ℝ) (501438858591/1000000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33529/262144 : ℝ))) 5 (501438858591/1000000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33529/262144 : ℝ))) 6 (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33529/262144 : ℝ))) 7 (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33529/262144 : ℝ)) hmem 8 (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33529/262144 : ℝ))) hcmem 8 (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33529/262144 : ℝ)) (992053778577/1000000000000 : ℝ) (49602688929/50000000000 : ℝ) (50143885859/100000000000 : ℝ) (501438858601/1000000000000 : ℝ) (793967357609/1000000000000 : ℝ) (79396735763/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0985_exp_lower
  have heNumeric : (2054901840773/1000000000000 : ℝ)/4 ≤ Real.exp (-17051296777203/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901840773/1000000000000 : ℝ)/4 ≤ Real.exp ((67057/524288 : ℝ)-(79396735763/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67057/524288 : ℝ) (33529/262144 : ℝ) (79396735763/100000000000 : ℝ) (2054901840773/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0986; no trusted numerical premise.
theorem cover8_leaf0986_exp_radius : (998003481762282731/1000000000000000000 : ℝ) ≤ Real.exp ((-67059/4194304 : ℝ)/8) ∧ Real.exp ((-67059/4194304 : ℝ)/8) ≤ (249500870440570683/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67059/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0986_exp_lower : (920113465257550223/1000000000000000000 : ℝ) ≤ Real.exp ((-42628241787959/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628241787959/64000000000000 : ℝ)/8) ≤ (57507091578596889/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628241787959/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0986_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901845751/1000000000000 : ℝ) ≤ 4*Real.exp (33529/262144 : ℝ)*Real.exp (-mu (radius 8 (67059/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901845751/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67059/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0986_exp_radius
  have hrNumeric : (492069509963/500000000000 : ℝ) ≤ Real.exp (-67059/4194304 : ℝ) ∧ Real.exp (-67059/4194304 : ℝ) ≤ (984139019927/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492069509963/500000000000 : ℝ) ≤ (radius 8 (67059/524288 : ℝ)) ∧ (radius 8 (67059/524288 : ℝ)) ≤ (984139019927/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67059/524288 : ℝ)) (492069509963/500000000000 : ℝ) (984139019927/1000000000000 : ℝ) (283838329/1600000000 : ℝ) (11087434727/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67059/524288 : ℝ)) (492069509963/500000000000 : ℝ) (984139019927/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67059/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492069509963/500000000000 : ℝ) (984139019927/1000000000000 : ℝ) (992069509963/1000000000000 : ℝ) (248017377491/250000000000 : ℝ) (496018905871/500000000000 : ℝ) (992037811743/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67059/524288 : ℝ)) 1 (992069509963/1000000000000 : ℝ) (248017377491/250000000000 : ℝ) (496018905871/500000000000 : ℝ) (992037811743/1000000000000 : ℝ) (248013415213/250000000000 : ℝ) (496026830427/500000000000 : ℝ) (39682146429/40000000000 : ℝ) (992053660727/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67059/524288 : ℝ)) 2 (248013415213/250000000000 : ℝ) (496026830427/500000000000 : ℝ) (39682146429/40000000000 : ℝ) (992053660727/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67059/524288 : ℝ)) 3 (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67059/524288 : ℝ)) 4 (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67059/524288 : ℝ)) 5 (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67059/524288 : ℝ)) 6 (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67059/524288 : ℝ)) 7 (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67059/524288 : ℝ))) (283838329/1600000000 : ℝ) (11087434727/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67059/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (283838329/1600000000 : ℝ) (11087434727/62500000000 : ℝ) (147174869453/250000000000 : ℝ) (73587434727/125000000000 : ℝ) (52648444247/125000000000 : ℝ) (210593776993/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67059/524288 : ℝ))) 1 (147174869453/250000000000 : ℝ) (73587434727/125000000000 : ℝ) (52648444247/125000000000 : ℝ) (210593776993/500000000000 : ℝ) (252471757947/500000000000 : ℝ) (504943515901/1000000000000 : ℝ) (248974342597/500000000000 : ℝ) (248974342601/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67059/524288 : ℝ))) 2 (252471757947/500000000000 : ℝ) (504943515901/1000000000000 : ℝ) (248974342597/500000000000 : ℝ) (248974342601/500000000000 : ℝ) (7835095321/15625000000 : ℝ) (62680762569/125000000000 : ℝ) (125358475939/250000000000 : ℝ) (100286780753/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67059/524288 : ℝ))) 3 (7835095321/15625000000 : ℝ) (62680762569/125000000000 : ℝ) (125358475939/250000000000 : ℝ) (100286780753/200000000000 : ℝ) (10028800043/20000000000 : ℝ) (501440002159/1000000000000 : ℝ) (7835000033/15625000000 : ℝ) (250720001061/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67059/524288 : ℝ))) 4 (10028800043/20000000000 : ℝ) (501440002159/1000000000000 : ℝ) (7835000033/15625000000 : ℝ) (250720001061/500000000000 : ℝ) (501440002131/1000000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67059/524288 : ℝ))) 5 (501440002131/1000000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67059/524288 : ℝ))) 6 (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67059/524288 : ℝ))) 7 (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67059/524288 : ℝ)) hmem 8 (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67059/524288 : ℝ))) hcmem 8 (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67059/524288 : ℝ)) (248013415197/250000000000 : ℝ) (992053660791/1000000000000 : ℝ) (50144000213/100000000000 : ℝ) (501440002141/1000000000000 : ℝ) (158793852507/200000000000 : ℝ) (198492315639/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0986_exp_lower
  have heNumeric : (2054901845751/1000000000000 : ℝ)/4 ≤ Real.exp (-42628241787959/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901845751/1000000000000 : ℝ)/4 ≤ Real.exp ((33529/262144 : ℝ)-(198492315639/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33529/262144 : ℝ) (67059/524288 : ℝ) (198492315639/250000000000 : ℝ) (2054901845751/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0987; no trusted numerical premise.
theorem cover8_leaf0987_exp_radius : (499001726009730833/500000000000000000 : ℝ) ≤ Real.exp ((-16765/1048576 : ℝ)/8) ∧ Real.exp ((-16765/1048576 : ℝ)/8) ≤ (998003452019461667/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16765/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0987_exp_lower : (460056732769186313/500000000000000000 : ℝ) ≤ Real.exp ((-85256483263389/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256483263389/128000000000000 : ℝ)/8) ≤ (920113465538372627/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256483263389/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0987_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901850769/1000000000000 : ℝ) ≤ 4*Real.exp (67059/524288 : ℝ)*Real.exp (-mu (radius 8 (16765/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901850769/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16765/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0987_exp_radius
  have hrNumeric : (984138785289/1000000000000 : ℝ) ≤ Real.exp (-16765/1048576 : ℝ) ∧ Real.exp (-16765/1048576 : ℝ) ≤ (98413878529/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984138785289/1000000000000 : ℝ) ≤ (radius 8 (16765/131072 : ℝ)) ∧ (radius 8 (16765/131072 : ℝ)) ≤ (98413878529/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16765/131072 : ℝ)) (984138785289/1000000000000 : ℝ) (98413878529/100000000000 : ℝ) (177400257293/1000000000000 : ℝ) (1774002573/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16765/131072 : ℝ)) (984138785289/1000000000000 : ℝ) (98413878529/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16765/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984138785289/1000000000000 : ℝ) (98413878529/100000000000 : ℝ) (248017348161/250000000000 : ℝ) (198413878529/200000000000 : ℝ) (992037693481/1000000000000 : ℝ) (992037693483/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16765/131072 : ℝ)) 1 (248017348161/250000000000 : ℝ) (198413878529/200000000000 : ℝ) (992037693481/1000000000000 : ℝ) (992037693483/1000000000000 : ℝ) (496026771531/500000000000 : ℝ) (124006692883/125000000000 : ℝ) (198410708587/200000000000 : ℝ) (496026771469/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16765/131072 : ℝ)) 2 (496026771531/500000000000 : ℝ) (124006692883/125000000000 : ℝ) (198410708587/200000000000 : ℝ) (496026771469/500000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16765/131072 : ℝ)) 3 (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16765/131072 : ℝ)) 4 (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16765/131072 : ℝ)) 5 (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16765/131072 : ℝ)) 6 (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16765/131072 : ℝ)) 7 (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16765/131072 : ℝ))) (177400257293/1000000000000 : ℝ) (1774002573/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16765/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177400257293/1000000000000 : ℝ) (1774002573/10000000000 : ℝ) (294350064323/500000000000 : ℝ) (11774002573/20000000000 : ℝ) (421189099209/1000000000000 : ℝ) (210594549609/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16765/131072 : ℝ))) 1 (294350064323/500000000000 : ℝ) (11774002573/20000000000 : ℝ) (421189099209/1000000000000 : ℝ) (210594549609/500000000000 : ℝ) (504944613927/1000000000000 : ℝ) (252472306967/500000000000 : ℝ) (497949873871/1000000000000 : ℝ) (497949873879/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16765/131072 : ℝ))) 2 (504944613927/1000000000000 : ℝ) (252472306967/500000000000 : ℝ) (497949873871/1000000000000 : ℝ) (497949873879/1000000000000 : ℝ) (501447243899/1000000000000 : ℝ) (501447243907/1000000000000 : ℝ) (100287009491/200000000000 : ℝ) (62679380933/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16765/131072 : ℝ))) 3 (501447243899/1000000000000 : ℝ) (501447243907/1000000000000 : ℝ) (100287009491/200000000000 : ℝ) (62679380933/125000000000 : ℝ) (501441145677/1000000000000 : ℝ) (250720572843/500000000000 : ℝ) (501441145639/1000000000000 : ℝ) (501441145649/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16765/131072 : ℝ))) 4 (501441145677/1000000000000 : ℝ) (250720572843/500000000000 : ℝ) (501441145639/1000000000000 : ℝ) (501441145649/1000000000000 : ℝ) (250720572829/500000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16765/131072 : ℝ))) 5 (250720572829/500000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16765/131072 : ℝ))) 6 (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16765/131072 : ℝ))) 7 (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16765/131072 : ℝ)) hmem 8 (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16765/131072 : ℝ))) hcmem 8 (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16765/131072 : ℝ)) (496026771499/500000000000 : ℝ) (992053543001/1000000000000 : ℝ) (501441145657/1000000000000 : ℝ) (125360286417/250000000000 : ℝ) (396985583721/500000000000 : ℝ) (793971167463/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0987_exp_lower
  have heNumeric : (2054901850769/1000000000000 : ℝ)/4 ≤ Real.exp (-85256483263389/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901850769/1000000000000 : ℝ)/4 ≤ Real.exp ((67059/524288 : ℝ)-(793971167463/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67059/524288 : ℝ) (16765/131072 : ℝ) (793971167463/1000000000000 : ℝ) (2054901850769/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0988; no trusted numerical premise.
theorem cover8_leaf0988_exp_radius : (998003422276641489/1000000000000000000 : ℝ) ≤ Real.exp ((-67061/4194304 : ℝ)/8) ∧ Real.exp ((-67061/4194304 : ℝ)/8) ≤ (99800342227664149/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67061/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0988_exp_lower : (460056732910747657/500000000000000000 : ℝ) ≤ Real.exp ((-852564829483/1280000000000 : ℝ)/8) ∧ Real.exp ((-852564829483/1280000000000 : ℝ)/8) ≤ (184022693164299063/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-852564829483/1280000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0988_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901855827/1000000000000 : ℝ) ≤ 4*Real.exp (16765/131072 : ℝ)*Real.exp (-mu (radius 8 (67061/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901855827/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67061/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0988_exp_radius
  have hrNumeric : (246034637663/250000000000 : ℝ) ≤ Real.exp (-67061/4194304 : ℝ) ∧ Real.exp (-67061/4194304 : ℝ) ≤ (984138550653/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246034637663/250000000000 : ℝ) ≤ (radius 8 (67061/524288 : ℝ)) ∧ (radius 8 (67061/524288 : ℝ)) ≤ (984138550653/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67061/524288 : ℝ)) (246034637663/250000000000 : ℝ) (984138550653/1000000000000 : ℝ) (22175194869/125000000000 : ℝ) (88700779479/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67061/524288 : ℝ)) (246034637663/250000000000 : ℝ) (984138550653/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67061/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246034637663/250000000000 : ℝ) (984138550653/1000000000000 : ℝ) (496034637663/500000000000 : ℝ) (992069275327/1000000000000 : ℝ) (992037575221/1000000000000 : ℝ) (992037575223/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67061/524288 : ℝ)) 1 (496034637663/500000000000 : ℝ) (992069275327/1000000000000 : ℝ) (992037575221/1000000000000 : ℝ) (992037575223/1000000000000 : ℝ) (992053425273/1000000000000 : ℝ) (39682137011/40000000000 : ℝ) (496026712573/500000000000 : ℝ) (992053425149/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67061/524288 : ℝ)) 2 (992053425273/1000000000000 : ℝ) (39682137011/40000000000 : ℝ) (496026712573/500000000000 : ℝ) (992053425149/1000000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67061/524288 : ℝ)) 3 (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67061/524288 : ℝ)) 4 (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67061/524288 : ℝ)) 5 (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67061/524288 : ℝ)) 6 (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67061/524288 : ℝ)) 7 (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67061/524288 : ℝ))) (22175194869/125000000000 : ℝ) (88700779479/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67061/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22175194869/125000000000 : ℝ) (88700779479/500000000000 : ℝ) (147175194869/250000000000 : ℝ) (588700779479/1000000000000 : ℝ) (210595322213/500000000000 : ℝ) (210595322217/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67061/524288 : ℝ))) 1 (147175194869/250000000000 : ℝ) (588700779479/1000000000000 : ℝ) (210595322213/500000000000 : ℝ) (210595322217/500000000000 : ℝ) (504945711951/1000000000000 : ℝ) (504945711957/1000000000000 : ℝ) (62243882817/125000000000 : ℝ) (497951062543/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67061/524288 : ℝ))) 2 (504945711951/1000000000000 : ℝ) (504945711957/1000000000000 : ℝ) (62243882817/125000000000 : ℝ) (497951062543/1000000000000 : ℝ) (501448387243/1000000000000 : ℝ) (2005793549/4000000000 : ℝ) (501436191143/1000000000000 : ℝ) (501436191151/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67061/524288 : ℝ))) 3 (501448387243/1000000000000 : ℝ) (2005793549/4000000000 : ℝ) (501436191143/1000000000000 : ℝ) (501436191151/1000000000000 : ℝ) (501442289193/1000000000000 : ℝ) (501442289201/1000000000000 : ℝ) (100288457831/200000000000 : ℝ) (125360572291/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67061/524288 : ℝ))) 4 (501442289193/1000000000000 : ℝ) (501442289201/1000000000000 : ℝ) (100288457831/200000000000 : ℝ) (125360572291/250000000000 : ℝ) (250721144587/500000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67061/524288 : ℝ))) 5 (250721144587/500000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67061/524288 : ℝ))) 6 (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67061/524288 : ℝ))) 7 (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67061/524288 : ℝ)) hmem 8 (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67061/524288 : ℝ))) hcmem 8 (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67061/524288 : ℝ)) (992053425209/1000000000000 : ℝ) (248013356303/250000000000 : ℝ) (501442289173/1000000000000 : ℝ) (501442289183/1000000000000 : ℝ) (793973072331/1000000000000 : ℝ) (15879461447/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0988_exp_lower
  have heNumeric : (2054901855827/1000000000000 : ℝ)/4 ≤ Real.exp (-852564829483/1280000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901855827/1000000000000 : ℝ)/4 ≤ Real.exp ((16765/131072 : ℝ)-(15879461447/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16765/131072 : ℝ) (67061/524288 : ℝ) (15879461447/20000000000 : ℝ) (2054901855827/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0989; no trusted numerical premise.
theorem cover8_leaf0989_exp_radius : (998003392533822197/1000000000000000000 : ℝ) ≤ Real.exp ((-33531/2097152 : ℝ)/8) ∧ Real.exp ((-33531/2097152 : ℝ)/8) ≤ (499001696266911099/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33531/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0989_exp_lower : (920113466106803271/1000000000000000000 : ℝ) ≤ Real.exp ((-85256482630779/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256482630779/128000000000000 : ℝ)/8) ≤ (115014183263350409/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256482630779/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0989_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725465231/250000000000 : ℝ) ≤ 4*Real.exp (67061/524288 : ℝ)*Real.exp (-mu (radius 8 (33531/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725465231/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33531/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0989_exp_radius
  have hrNumeric : (196827663203/200000000000 : ℝ) ≤ Real.exp (-33531/2097152 : ℝ) ∧ Real.exp (-33531/2097152 : ℝ) ≤ (61508644751/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196827663203/200000000000 : ℝ) ≤ (radius 8 (33531/262144 : ℝ)) ∧ (radius 8 (33531/262144 : ℝ)) ≤ (61508644751/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33531/262144 : ℝ)) (196827663203/200000000000 : ℝ) (61508644751/62500000000 : ℝ) (887014303/5000000000 : ℝ) (88701430303/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33531/262144 : ℝ)) (196827663203/200000000000 : ℝ) (61508644751/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33531/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196827663203/200000000000 : ℝ) (61508644751/62500000000 : ℝ) (992069158007/1000000000000 : ℝ) (124008644751/125000000000 : ℝ) (992037456961/1000000000000 : ℝ) (992037456963/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33531/262144 : ℝ)) 1 (992069158007/1000000000000 : ℝ) (124008644751/125000000000 : ℝ) (992037456961/1000000000000 : ℝ) (992037456963/1000000000000 : ℝ) (248013326871/250000000000 : ℝ) (496026653743/500000000000 : ℝ) (992053307357/1000000000000 : ℝ) (992053307359/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33531/262144 : ℝ)) 2 (248013326871/250000000000 : ℝ) (496026653743/500000000000 : ℝ) (992053307357/1000000000000 : ℝ) (992053307359/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33531/262144 : ℝ)) 3 (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33531/262144 : ℝ)) 4 (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33531/262144 : ℝ)) 5 (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33531/262144 : ℝ)) 6 (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33531/262144 : ℝ)) 7 (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33531/262144 : ℝ))) (887014303/5000000000 : ℝ) (88701430303/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33531/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (887014303/5000000000 : ℝ) (88701430303/500000000000 : ℝ) (5887014303/10000000000 : ℝ) (588701430303/1000000000000 : ℝ) (421192189623/1000000000000 : ℝ) (421192189631/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33531/262144 : ℝ))) 1 (5887014303/10000000000 : ℝ) (588701430303/1000000000000 : ℝ) (421192189623/1000000000000 : ℝ) (421192189631/1000000000000 : ℝ) (504946809961/1000000000000 : ℝ) (504946809967/1000000000000 : ℝ) (497952251187/1000000000000 : ℝ) (248976125597/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33531/262144 : ℝ))) 2 (504946809961/1000000000000 : ℝ) (504946809967/1000000000000 : ℝ) (497952251187/1000000000000 : ℝ) (248976125597/500000000000 : ℝ) (250724765287/500000000000 : ℝ) (501449530581/1000000000000 : ℝ) (250718667409/500000000000 : ℝ) (20057493393/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33531/262144 : ℝ))) 3 (250724765287/500000000000 : ℝ) (501449530581/1000000000000 : ℝ) (250718667409/500000000000 : ℝ) (20057493393/40000000000 : ℝ) (62680429087/125000000000 : ℝ) (501443432703/1000000000000 : ℝ) (250721716329/500000000000 : ℝ) (250721716333/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33531/262144 : ℝ))) 4 (62680429087/125000000000 : ℝ) (501443432703/1000000000000 : ℝ) (250721716329/500000000000 : ℝ) (250721716333/500000000000 : ℝ) (501443432677/1000000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33531/262144 : ℝ))) 5 (501443432677/1000000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33531/262144 : ℝ))) 6 (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33531/262144 : ℝ))) 7 (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33531/262144 : ℝ)) hmem 8 (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33531/262144 : ℝ))) hcmem 8 (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33531/262144 : ℝ)) (49602665371/50000000000 : ℝ) (992053307423/1000000000000 : ℝ) (125360858169/250000000000 : ℝ) (100288686537/200000000000 : ℝ) (1984937443/2500000000 : ℝ) (396987488609/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0989_exp_lower
  have heNumeric : (513725465231/250000000000 : ℝ)/4 ≤ Real.exp (-85256482630779/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725465231/250000000000 : ℝ)/4 ≤ Real.exp ((67061/524288 : ℝ)-(396987488609/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67061/524288 : ℝ) (33531/262144 : ℝ) (396987488609/500000000000 : ℝ) (513725465231/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0990; no trusted numerical premise.
theorem cover8_leaf0990_exp_radius : (62375210174437737/62500000000000000 : ℝ) ≤ Real.exp ((-67063/4194304 : ℝ)/8) ∧ Real.exp ((-67063/4194304 : ℝ)/8) ≤ (998003362791003793/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67063/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0990_exp_lower : (460056733196975727/500000000000000000 : ℝ) ≤ Real.exp ((-8525648231121/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525648231121/12800000000000 : ℝ)/8) ≤ (184022693278790291/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525648231121/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0990_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980373211/200000000000 : ℝ) ≤ 4*Real.exp (33531/262144 : ℝ)*Real.exp (-mu (radius 8 (67063/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980373211/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67063/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0990_exp_radius
  have hrNumeric : (492069040689/500000000000 : ℝ) ≤ Real.exp (-67063/4194304 : ℝ) ∧ Real.exp (-67063/4194304 : ℝ) ≤ (984138081379/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492069040689/500000000000 : ℝ) ≤ (radius 8 (67063/524288 : ℝ)) ∧ (radius 8 (67063/524288 : ℝ)) ≤ (984138081379/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67063/524288 : ℝ)) (492069040689/500000000000 : ℝ) (984138081379/1000000000000 : ℝ) (88702081119/500000000000 : ℝ) (35480832449/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67063/524288 : ℝ)) (492069040689/500000000000 : ℝ) (984138081379/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67063/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492069040689/500000000000 : ℝ) (984138081379/1000000000000 : ℝ) (992069040689/1000000000000 : ℝ) (99206904069/100000000000 : ℝ) (992037338701/1000000000000 : ℝ) (992037338703/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67063/524288 : ℝ)) 1 (992069040689/1000000000000 : ℝ) (99206904069/100000000000 : ℝ) (992037338701/1000000000000 : ℝ) (992037338703/1000000000000 : ℝ) (198410637939/200000000000 : ℝ) (992053189697/1000000000000 : ℝ) (15500831087/15625000000 : ℝ) (99205318957/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67063/524288 : ℝ)) 2 (198410637939/200000000000 : ℝ) (992053189697/1000000000000 : ℝ) (15500831087/15625000000 : ℝ) (99205318957/100000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67063/524288 : ℝ)) 3 (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67063/524288 : ℝ)) 4 (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67063/524288 : ℝ)) 5 (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67063/524288 : ℝ)) 6 (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67063/524288 : ℝ)) 7 (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67063/524288 : ℝ))) (88702081119/500000000000 : ℝ) (35480832449/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67063/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88702081119/500000000000 : ℝ) (35480832449/200000000000 : ℝ) (588702081119/1000000000000 : ℝ) (588702081123/1000000000000 : ℝ) (421193734803/1000000000000 : ℝ) (421193734813/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67063/524288 : ℝ))) 1 (588702081119/1000000000000 : ℝ) (588702081123/1000000000000 : ℝ) (421193734803/1000000000000 : ℝ) (421193734813/1000000000000 : ℝ) (504947907961/1000000000000 : ℝ) (3944905531/7812500000 : ℝ) (31122089989/62500000000 : ℝ) (62244179979/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67063/524288 : ℝ))) 2 (504947907961/1000000000000 : ℝ) (3944905531/7812500000 : ℝ) (31122089989/62500000000 : ℝ) (62244179979/125000000000 : ℝ) (125362668473/250000000000 : ℝ) (5014506739/10000000000 : ℝ) (6267980981/12500000000 : ℝ) (501438478489/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67063/524288 : ℝ))) 3 (125362668473/250000000000 : ℝ) (5014506739/10000000000 : ℝ) (6267980981/12500000000 : ℝ) (501438478489/1000000000000 : ℝ) (250722288093/500000000000 : ℝ) (100288915239/200000000000 : ℝ) (125361144037/250000000000 : ℝ) (250722288079/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67063/524288 : ℝ))) 4 (250722288093/500000000000 : ℝ) (100288915239/200000000000 : ℝ) (125361144037/250000000000 : ℝ) (250722288079/500000000000 : ℝ) (501444576167/1000000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67063/524288 : ℝ))) 5 (501444576167/1000000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67063/524288 : ℝ))) 6 (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67063/524288 : ℝ))) 7 (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67063/524288 : ℝ)) hmem 8 (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67063/524288 : ℝ))) hcmem 8 (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67063/524288 : ℝ)) (992053189631/1000000000000 : ℝ) (496026594817/500000000000 : ℝ) (250722288083/500000000000 : ℝ) (501444576177/1000000000000 : ℝ) (793976882049/1000000000000 : ℝ) (79397688207/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0990_exp_lower
  have heNumeric : (410980373211/200000000000 : ℝ)/4 ≤ Real.exp (-8525648231121/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980373211/200000000000 : ℝ)/4 ≤ Real.exp ((33531/262144 : ℝ)-(79397688207/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33531/262144 : ℝ) (67063/524288 : ℝ) (79397688207/100000000000 : ℝ) (410980373211/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0991; no trusted numerical premise.
theorem cover8_leaf0991_exp_radius : (998003333048186273/1000000000000000000 : ℝ) ≤ Real.exp ((-8383/524288 : ℝ)/8) ∧ Real.exp ((-8383/524288 : ℝ)/8) ≤ (499001666524093137/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8383/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0991_exp_lower : (57507091667784379/62500000000000000 : ℝ) ≤ Real.exp ((-85256481987801/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256481987801/128000000000000 : ℝ)/8) ≤ (184022693336910013/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256481987801/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0991_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901871247/1000000000000 : ℝ) ≤ 4*Real.exp (67063/524288 : ℝ)*Real.exp (-mu (radius 8 (8383/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901871247/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8383/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0991_exp_radius
  have hrNumeric : (492068923371/500000000000 : ℝ) ≤ Real.exp (-8383/524288 : ℝ) ∧ Real.exp (-8383/524288 : ℝ) ≤ (984137846743/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492068923371/500000000000 : ℝ) ≤ (radius 8 (8383/65536 : ℝ)) ∧ (radius 8 (8383/65536 : ℝ)) ≤ (984137846743/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8383/65536 : ℝ)) (492068923371/500000000000 : ℝ) (984137846743/1000000000000 : ℝ) (177405463861/1000000000000 : ℝ) (44351365967/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8383/65536 : ℝ)) (492068923371/500000000000 : ℝ) (984137846743/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8383/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492068923371/500000000000 : ℝ) (984137846743/1000000000000 : ℝ) (992068923371/1000000000000 : ℝ) (248017230843/250000000000 : ℝ) (992037220441/1000000000000 : ℝ) (992037220443/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8383/65536 : ℝ)) 1 (992068923371/1000000000000 : ℝ) (248017230843/250000000000 : ℝ) (992037220441/1000000000000 : ℝ) (992037220443/1000000000000 : ℝ) (496026535953/500000000000 : ℝ) (248013267977/250000000000 : ℝ) (992053071779/1000000000000 : ℝ) (992053071781/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8383/65536 : ℝ)) 2 (496026535953/500000000000 : ℝ) (248013267977/250000000000 : ℝ) (992053071779/1000000000000 : ℝ) (992053071781/1000000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8383/65536 : ℝ)) 3 (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8383/65536 : ℝ)) 4 (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8383/65536 : ℝ)) 5 (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8383/65536 : ℝ)) 6 (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8383/65536 : ℝ)) 7 (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8383/65536 : ℝ))) (177405463861/1000000000000 : ℝ) (44351365967/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8383/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177405463861/1000000000000 : ℝ) (44351365967/250000000000 : ℝ) (58870273193/100000000000 : ℝ) (294351365967/500000000000 : ℝ) (10529881999/25000000000 : ℝ) (421195279969/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8383/65536 : ℝ))) 1 (58870273193/100000000000 : ℝ) (294351365967/500000000000 : ℝ) (10529881999/25000000000 : ℝ) (421195279969/1000000000000 : ℝ) (100989801189/200000000000 : ℝ) (3944914109/7812500000 : ℝ) (497954628443/1000000000000 : ℝ) (497954628451/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8383/65536 : ℝ))) 2 (100989801189/200000000000 : ℝ) (3944914109/7812500000 : ℝ) (497954628443/1000000000000 : ℝ) (497954628451/1000000000000 : ℝ) (250725908597/500000000000 : ℝ) (250725908601/500000000000 : ℝ) (250719811063/500000000000 : ℝ) (250719811067/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8383/65536 : ℝ))) 3 (250725908597/500000000000 : ℝ) (250725908601/500000000000 : ℝ) (250719811063/500000000000 : ℝ) (250719811067/500000000000 : ℝ) (25072285983/50000000000 : ℝ) (125361429917/250000000000 : ℝ) (250722859811/500000000000 : ℝ) (501445719631/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8383/65536 : ℝ))) 4 (25072285983/50000000000 : ℝ) (125361429917/250000000000 : ℝ) (250722859811/500000000000 : ℝ) (501445719631/1000000000000 : ℝ) (501445719641/1000000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8383/65536 : ℝ))) 5 (501445719641/1000000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8383/65536 : ℝ))) 6 (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8383/65536 : ℝ))) 7 (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8383/65536 : ℝ)) hmem 8 (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8383/65536 : ℝ))) hcmem 8 (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8383/65536 : ℝ)) (496026535921/500000000000 : ℝ) (198410614369/200000000000 : ℝ) (12536142991/25000000000 : ℝ) (10028914393/20000000000 : ℝ) (793978786873/1000000000000 : ℝ) (198494696723/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0991_exp_lower
  have heNumeric : (2054901871247/1000000000000 : ℝ)/4 ≤ Real.exp (-85256481987801/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901871247/1000000000000 : ℝ)/4 ≤ Real.exp ((67063/524288 : ℝ)-(198494696723/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67063/524288 : ℝ) (8383/65536 : ℝ) (198494696723/250000000000 : ℝ) (2054901871247/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0992; no trusted numerical premise.
theorem cover8_leaf0992_exp_radius : (998003303305369641/1000000000000000000 : ℝ) ≤ Real.exp ((-67065/4194304 : ℝ)/8) ∧ Real.exp ((-67065/4194304 : ℝ)/8) ≤ (499001651652684821/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67065/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0992_exp_lower : (920113466976068787/1000000000000000000 : ℝ) ≤ Real.exp ((-10657060207921/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657060207921/16000000000000 : ℝ)/8) ≤ (230028366744017197/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657060207921/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0992_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980375291/200000000000 : ℝ) ≤ 4*Real.exp (8383/65536 : ℝ)*Real.exp (-mu (radius 8 (67065/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980375291/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67065/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0992_exp_radius
  have hrNumeric : (196827522421/200000000000 : ℝ) ≤ Real.exp (-67065/4194304 : ℝ) ∧ Real.exp (-67065/4194304 : ℝ) ≤ (492068806053/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196827522421/200000000000 : ℝ) ≤ (radius 8 (67065/524288 : ℝ)) ∧ (radius 8 (67065/524288 : ℝ)) ≤ (492068806053/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67065/524288 : ℝ)) (196827522421/200000000000 : ℝ) (492068806053/500000000000 : ℝ) (4435169137/25000000000 : ℝ) (177406765487/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67065/524288 : ℝ)) (196827522421/200000000000 : ℝ) (492068806053/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67065/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196827522421/200000000000 : ℝ) (492068806053/500000000000 : ℝ) (248017201513/250000000000 : ℝ) (992068806053/1000000000000 : ℝ) (992037102181/1000000000000 : ℝ) (992037102183/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67065/524288 : ℝ)) 1 (248017201513/250000000000 : ℝ) (992068806053/1000000000000 : ℝ) (992037102181/1000000000000 : ℝ) (992037102183/1000000000000 : ℝ) (248013238529/250000000000 : ℝ) (496026477059/500000000000 : ℝ) (992052953989/1000000000000 : ℝ) (124006619249/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67065/524288 : ℝ)) 2 (248013238529/250000000000 : ℝ) (496026477059/500000000000 : ℝ) (992052953989/1000000000000 : ℝ) (124006619249/125000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67065/524288 : ℝ)) 3 (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67065/524288 : ℝ)) 4 (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67065/524288 : ℝ)) 5 (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67065/524288 : ℝ)) 6 (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67065/524288 : ℝ)) 7 (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67065/524288 : ℝ))) (4435169137/25000000000 : ℝ) (177406765487/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67065/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4435169137/25000000000 : ℝ) (177406765487/1000000000000 : ℝ) (29435169137/50000000000 : ℝ) (73587922843/125000000000 : ℝ) (210598412553/500000000000 : ℝ) (105299206279/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67065/524288 : ℝ))) 1 (29435169137/50000000000 : ℝ) (73587922843/125000000000 : ℝ) (210598412553/500000000000 : ℝ) (105299206279/250000000000 : ℝ) (504950103923/1000000000000 : ℝ) (50495010393/100000000000 : ℝ) (99591163411/200000000000 : ℝ) (497955817063/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67065/524288 : ℝ))) 2 (504950103923/1000000000000 : ℝ) (50495010393/100000000000 : ℝ) (99591163411/200000000000 : ℝ) (497955817063/1000000000000 : ℝ) (501452960489/1000000000000 : ℝ) (501452960497/1000000000000 : ℝ) (125360191441/250000000000 : ℝ) (501440765773/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67065/524288 : ℝ))) 3 (501452960489/1000000000000 : ℝ) (501452960497/1000000000000 : ℝ) (125360191441/250000000000 : ℝ) (501440765773/1000000000000 : ℝ) (250723431563/500000000000 : ℝ) (100289372627/200000000000 : ℝ) (501446863089/1000000000000 : ℝ) (250723431549/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67065/524288 : ℝ))) 4 (250723431563/500000000000 : ℝ) (100289372627/200000000000 : ℝ) (501446863089/1000000000000 : ℝ) (250723431549/500000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67065/524288 : ℝ))) 5 (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67065/524288 : ℝ))) 6 (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67065/524288 : ℝ))) 7 (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67065/524288 : ℝ)) hmem 8 (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67065/524288 : ℝ))) hcmem 8 (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67065/524288 : ℝ)) (248013238513/250000000000 : ℝ) (198410590811/200000000000 : ℝ) (501446863107/1000000000000 : ℝ) (501446863117/1000000000000 : ℝ) (793980691687/1000000000000 : ℝ) (396990345853/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0992_exp_lower
  have heNumeric : (410980375291/200000000000 : ℝ)/4 ≤ Real.exp (-10657060207921/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980375291/200000000000 : ℝ)/4 ≤ Real.exp ((8383/65536 : ℝ)-(396990345853/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8383/65536 : ℝ) (67065/524288 : ℝ) (396990345853/500000000000 : ℝ) (410980375291/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0993; no trusted numerical premise.
theorem cover8_leaf0993_exp_radius : (199600654712510779/200000000000000000 : ℝ) ≤ Real.exp ((-33533/2097152 : ℝ)/8) ∧ Real.exp ((-33533/2097152 : ℝ)/8) ≤ (124750409195319237/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33533/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0993_exp_lower : (460056733634943897/500000000000000000 : ℝ) ≤ Real.exp ((-682051850691/1024000000000 : ℝ)/8) ∧ Real.exp ((-682051850691/1024000000000 : ℝ)/8) ≤ (184022693453977559/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682051850691/1024000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0993_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980376341/200000000000 : ℝ) ≤ 4*Real.exp (67065/524288 : ℝ)*Real.exp (-mu (radius 8 (33533/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980376341/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33533/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0993_exp_radius
  have hrNumeric : (246034344367/250000000000 : ℝ) ≤ Real.exp (-33533/2097152 : ℝ) ∧ Real.exp (-33533/2097152 : ℝ) ≤ (984137377469/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246034344367/250000000000 : ℝ) ≤ (radius 8 (33533/262144 : ℝ)) ∧ (radius 8 (33533/262144 : ℝ)) ≤ (984137377469/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33533/262144 : ℝ)) (246034344367/250000000000 : ℝ) (984137377469/1000000000000 : ℝ) (177408067089/1000000000000 : ℝ) (22176008387/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33533/262144 : ℝ)) (246034344367/250000000000 : ℝ) (984137377469/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33533/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246034344367/250000000000 : ℝ) (984137377469/1000000000000 : ℝ) (496034344367/500000000000 : ℝ) (198413737747/200000000000 : ℝ) (992036983921/1000000000000 : ℝ) (496018491961/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33533/262144 : ℝ)) 1 (496034344367/500000000000 : ℝ) (198413737747/200000000000 : ℝ) (992036983921/1000000000000 : ℝ) (496018491961/500000000000 : ℝ) (992052836327/1000000000000 : ℝ) (992052836329/1000000000000 : ℝ) (4960264181/5000000000 : ℝ) (496026418101/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33533/262144 : ℝ)) 2 (992052836327/1000000000000 : ℝ) (992052836329/1000000000000 : ℝ) (4960264181/5000000000 : ℝ) (496026418101/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33533/262144 : ℝ)) 3 (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33533/262144 : ℝ)) 4 (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33533/262144 : ℝ)) 5 (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33533/262144 : ℝ)) 6 (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33533/262144 : ℝ)) 7 (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33533/262144 : ℝ))) (177408067089/1000000000000 : ℝ) (22176008387/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33533/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177408067089/1000000000000 : ℝ) (22176008387/125000000000 : ℝ) (73588004193/125000000000 : ℝ) (147176008387/250000000000 : ℝ) (84239674047/200000000000 : ℝ) (105299592561/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33533/262144 : ℝ))) 1 (73588004193/125000000000 : ℝ) (147176008387/250000000000 : ℝ) (84239674047/200000000000 : ℝ) (105299592561/250000000000 : ℝ) (504951201889/1000000000000 : ℝ) (63118900237/125000000000 : ℝ) (497957005653/1000000000000 : ℝ) (497957005661/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33533/262144 : ℝ))) 2 (504951201889/1000000000000 : ℝ) (63118900237/125000000000 : ℝ) (497957005653/1000000000000 : ℝ) (497957005661/1000000000000 : ℝ) (501454103771/1000000000000 : ℝ) (501454103779/1000000000000 : ℝ) (50144190939/100000000000 : ℝ) (501441909399/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33533/262144 : ℝ))) 3 (501454103771/1000000000000 : ℝ) (501454103779/1000000000000 : ℝ) (50144190939/100000000000 : ℝ) (501441909399/1000000000000 : ℝ) (25072400329/50000000000 : ℝ) (501448006589/1000000000000 : ℝ) (501448006543/1000000000000 : ℝ) (62681000819/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33533/262144 : ℝ))) 4 (25072400329/50000000000 : ℝ) (501448006589/1000000000000 : ℝ) (501448006543/1000000000000 : ℝ) (62681000819/125000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33533/262144 : ℝ))) 5 (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33533/262144 : ℝ))) 6 (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33533/262144 : ℝ))) 7 (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33533/262144 : ℝ)) hmem 8 (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33533/262144 : ℝ))) hcmem 8 (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33533/262144 : ℝ)) (992052836263/1000000000000 : ℝ) (496026418133/500000000000 : ℝ) (501448006561/1000000000000 : ℝ) (501448006571/1000000000000 : ℝ) (1240597807/1562500000 : ℝ) (1587965193/2000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0993_exp_lower
  have heNumeric : (410980376341/200000000000 : ℝ)/4 ≤ Real.exp (-682051850691/1024000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980376341/200000000000 : ℝ)/4 ≤ Real.exp ((67065/524288 : ℝ)-(1587965193/2000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67065/524288 : ℝ) (33533/262144 : ℝ) (1587965193/2000000000 : ℝ) (410980376341/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0994; no trusted numerical premise.
theorem cover8_leaf0994_exp_radius : (249500810954934759/250000000000000000 : ℝ) ≤ Real.exp ((-67067/4194304 : ℝ)/8) ∧ Real.exp ((-67067/4194304 : ℝ)/8) ≤ (998003243819739037/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67067/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0994_exp_lower : (460056733783463599/500000000000000000 : ℝ) ≤ Real.exp ((-42628240502899/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628240502899/64000000000000 : ℝ)/8) ≤ (920113467566927199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628240502899/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0994_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725471753/250000000000 : ℝ) ≤ 4*Real.exp (33533/262144 : ℝ)*Real.exp (-mu (radius 8 (67067/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725471753/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67067/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0994_exp_radius
  have hrNumeric : (61508571427/62500000000 : ℝ) ≤ Real.exp (-67067/4194304 : ℝ) ∧ Real.exp (-67067/4194304 : ℝ) ≤ (984137142833/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61508571427/62500000000 : ℝ) ≤ (radius 8 (67067/524288 : ℝ)) ∧ (radius 8 (67067/524288 : ℝ)) ≤ (984137142833/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67067/524288 : ℝ)) (61508571427/62500000000 : ℝ) (984137142833/1000000000000 : ℝ) (88704684341/500000000000 : ℝ) (177409368689/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67067/524288 : ℝ)) (61508571427/62500000000 : ℝ) (984137142833/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67067/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61508571427/62500000000 : ℝ) (984137142833/1000000000000 : ℝ) (124008571427/125000000000 : ℝ) (992068571417/1000000000000 : ℝ) (992036865661/1000000000000 : ℝ) (992036865663/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67067/524288 : ℝ)) 1 (124008571427/125000000000 : ℝ) (992068571417/1000000000000 : ℝ) (992036865661/1000000000000 : ℝ) (992036865663/1000000000000 : ℝ) (496026359269/500000000000 : ℝ) (49602635927/50000000000 : ℝ) (992052718411/1000000000000 : ℝ) (496026359207/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67067/524288 : ℝ)) 2 (496026359269/500000000000 : ℝ) (49602635927/50000000000 : ℝ) (992052718411/1000000000000 : ℝ) (496026359207/500000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67067/524288 : ℝ)) 3 (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67067/524288 : ℝ)) 4 (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67067/524288 : ℝ)) 5 (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67067/524288 : ℝ)) 6 (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67067/524288 : ℝ)) 7 (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67067/524288 : ℝ))) (88704684341/500000000000 : ℝ) (177409368689/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67067/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88704684341/500000000000 : ℝ) (177409368689/1000000000000 : ℝ) (588704684341/1000000000000 : ℝ) (117740936869/200000000000 : ℝ) (421199915339/1000000000000 : ℝ) (105299978837/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67067/524288 : ℝ))) 1 (588704684341/1000000000000 : ℝ) (117740936869/200000000000 : ℝ) (421199915339/1000000000000 : ℝ) (105299978837/250000000000 : ℝ) (1577975937/3125000000 : ℝ) (504952299847/1000000000000 : ℝ) (497958194233/1000000000000 : ℝ) (497958194241/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67067/524288 : ℝ))) 2 (1577975937/3125000000 : ℝ) (504952299847/1000000000000 : ℝ) (497958194233/1000000000000 : ℝ) (497958194241/1000000000000 : ℝ) (125363811759/250000000000 : ℝ) (125363811761/250000000000 : ℝ) (501443053/1000000000 : ℝ) (31340190813/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67067/524288 : ℝ))) 3 (125363811759/250000000000 : ℝ) (125363811761/250000000000 : ℝ) (501443053/1000000000 : ℝ) (31340190813/62500000000 : ℝ) (250724575009/500000000000 : ℝ) (250724575013/500000000000 : ℝ) (25072457499/50000000000 : ℝ) (501449149989/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67067/524288 : ℝ))) 4 (250724575009/500000000000 : ℝ) (250724575013/500000000000 : ℝ) (25072457499/50000000000 : ℝ) (501449149989/1000000000000 : ℝ) (501449149999/1000000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67067/524288 : ℝ))) 5 (501449149999/1000000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67067/524288 : ℝ))) 6 (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67067/524288 : ℝ))) 7 (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67067/524288 : ℝ)) hmem 8 (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67067/524288 : ℝ))) hcmem 8 (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67067/524288 : ℝ)) (496026359237/500000000000 : ℝ) (992052718477/1000000000000 : ℝ) (250724574999/500000000000 : ℝ) (62681143751/125000000000 : ℝ) (793984501247/1000000000000 : ℝ) (396992250633/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0994_exp_lower
  have heNumeric : (513725471753/250000000000 : ℝ)/4 ≤ Real.exp (-42628240502899/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725471753/250000000000 : ℝ)/4 ≤ Real.exp ((33533/262144 : ℝ)-(396992250633/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33533/262144 : ℝ) (67067/524288 : ℝ) (396992250633/500000000000 : ℝ) (513725471753/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0995; no trusted numerical premise.
theorem cover8_leaf0995_exp_radius : (499001607038462531/500000000000000000 : ℝ) ≤ Real.exp ((-16767/1048576 : ℝ)/8) ∧ Real.exp ((-16767/1048576 : ℝ)/8) ≤ (998003214076925063/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16767/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0995_exp_lower : (115014183483139593/125000000000000000 : ℝ) ≤ Real.exp ((-85256480673941/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256480673941/128000000000000 : ℝ)/8) ≤ (184022693573023349/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256480673941/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0995_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901892339/1000000000000 : ℝ) ≤ 4*Real.exp (67067/524288 : ℝ)*Real.exp (-mu (radius 8 (16767/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901892339/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16767/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0995_exp_radius
  have hrNumeric : (196827381639/200000000000 : ℝ) ≤ Real.exp (-16767/1048576 : ℝ) ∧ Real.exp (-16767/1048576 : ℝ) ≤ (246034227049/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196827381639/200000000000 : ℝ) ≤ (radius 8 (16767/131072 : ℝ)) ∧ (radius 8 (16767/131072 : ℝ)) ≤ (246034227049/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16767/131072 : ℝ)) (196827381639/200000000000 : ℝ) (246034227049/250000000000 : ℝ) (2772041723/15625000000 : ℝ) (88705335139/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16767/131072 : ℝ)) (196827381639/200000000000 : ℝ) (246034227049/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16767/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196827381639/200000000000 : ℝ) (246034227049/250000000000 : ℝ) (992068454097/1000000000000 : ℝ) (496034227049/500000000000 : ℝ) (992036747401/1000000000000 : ℝ) (992036747403/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16767/131072 : ℝ)) 1 (992068454097/1000000000000 : ℝ) (496034227049/500000000000 : ℝ) (992036747401/1000000000000 : ℝ) (992036747403/1000000000000 : ℝ) (992052600749/1000000000000 : ℝ) (992052600751/1000000000000 : ℝ) (496026300311/500000000000 : ℝ) (62003287539/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16767/131072 : ℝ)) 2 (992052600749/1000000000000 : ℝ) (992052600751/1000000000000 : ℝ) (496026300311/500000000000 : ℝ) (62003287539/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16767/131072 : ℝ)) 3 (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16767/131072 : ℝ)) 4 (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16767/131072 : ℝ)) 5 (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16767/131072 : ℝ)) 6 (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16767/131072 : ℝ)) 7 (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16767/131072 : ℝ))) (2772041723/15625000000 : ℝ) (88705335139/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16767/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2772041723/15625000000 : ℝ) (88705335139/500000000000 : ℝ) (18397041723/31250000000 : ℝ) (588705335139/1000000000000 : ℝ) (210600730217/500000000000 : ℝ) (210600730221/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16767/131072 : ℝ))) 1 (18397041723/31250000000 : ℝ) (588705335139/1000000000000 : ℝ) (210600730217/500000000000 : ℝ) (210600730221/500000000000 : ℝ) (100990679557/200000000000 : ℝ) (504953397791/1000000000000 : ℝ) (248979691403/500000000000 : ℝ) (497959382813/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16767/131072 : ℝ))) 2 (100990679557/200000000000 : ℝ) (504953397791/1000000000000 : ℝ) (248979691403/500000000000 : ℝ) (497959382813/1000000000000 : ℝ) (100291278059/200000000000 : ℝ) (250728195151/500000000000 : ℝ) (250722098301/500000000000 : ℝ) (50144419661/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16767/131072 : ℝ))) 3 (100291278059/200000000000 : ℝ) (250728195151/500000000000 : ℝ) (250722098301/500000000000 : ℝ) (50144419661/100000000000 : ℝ) (62681286681/125000000000 : ℝ) (31340643341/62500000000 : ℝ) (501450293411/1000000000000 : ℝ) (501450293419/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16767/131072 : ℝ))) 4 (62681286681/125000000000 : ℝ) (31340643341/62500000000 : ℝ) (501450293411/1000000000000 : ℝ) (501450293419/1000000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16767/131072 : ℝ))) 5 (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16767/131072 : ℝ))) 6 (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16767/131072 : ℝ))) 7 (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16767/131072 : ℝ)) hmem 8 (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16767/131072 : ℝ))) hcmem 8 (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16767/131072 : ℝ)) (198410520137/200000000000 : ℝ) (62003287543/62500000000 : ℝ) (501450293429/1000000000000 : ℝ) (250725146719/500000000000 : ℝ) (158797281201/200000000000 : ℝ) (396993203011/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0995_exp_lower
  have heNumeric : (2054901892339/1000000000000 : ℝ)/4 ≤ Real.exp (-85256480673941/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901892339/1000000000000 : ℝ)/4 ≤ Real.exp ((67067/524288 : ℝ)-(396993203011/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67067/524288 : ℝ) (16767/131072 : ℝ) (396993203011/500000000000 : ℝ) (2054901892339/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0996; no trusted numerical premise.
theorem cover8_leaf0996_exp_radius : (124750398041763997/125000000000000000 : ℝ) ≤ Real.exp ((-67069/4194304 : ℝ)/8) ∧ Real.exp ((-67069/4194304 : ℝ)/8) ≤ (998003184334111977/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67069/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0996_exp_lower : (184022693633075309/200000000000000000 : ℝ) ≤ Real.exp ((-4262824016989/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262824016989/6400000000000 : ℝ)/8) ≤ (460056734082688273/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262824016989/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0996_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862737213/125000000000 : ℝ) ≤ 4*Real.exp (16767/131072 : ℝ)*Real.exp (-mu (radius 8 (67069/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862737213/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67069/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0996_exp_radius
  have hrNumeric : (492068336779/500000000000 : ℝ) ≤ Real.exp (-67069/4194304 : ℝ) ∧ Real.exp (-67069/4194304 : ℝ) ≤ (984136673559/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492068336779/500000000000 : ℝ) ≤ (radius 8 (67069/524288 : ℝ)) ∧ (radius 8 (67069/524288 : ℝ)) ≤ (984136673559/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67069/524288 : ℝ)) (492068336779/500000000000 : ℝ) (984136673559/1000000000000 : ℝ) (177411971851/1000000000000 : ℝ) (88705985929/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67069/524288 : ℝ)) (492068336779/500000000000 : ℝ) (984136673559/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67069/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492068336779/500000000000 : ℝ) (984136673559/1000000000000 : ℝ) (992068336779/1000000000000 : ℝ) (49603416839/50000000000 : ℝ) (992036629141/1000000000000 : ℝ) (496018314571/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67069/524288 : ℝ)) 1 (992068336779/1000000000000 : ℝ) (49603416839/50000000000 : ℝ) (992036629141/1000000000000 : ℝ) (496018314571/500000000000 : ℝ) (12400656037/12500000000 : ℝ) (992052482961/1000000000000 : ℝ) (992052482833/1000000000000 : ℝ) (198410496567/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67069/524288 : ℝ)) 2 (12400656037/12500000000 : ℝ) (992052482961/1000000000000 : ℝ) (992052482833/1000000000000 : ℝ) (198410496567/200000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67069/524288 : ℝ)) 3 (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67069/524288 : ℝ)) 4 (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67069/524288 : ℝ)) 5 (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67069/524288 : ℝ)) 6 (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67069/524288 : ℝ)) 7 (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67069/524288 : ℝ))) (177411971851/1000000000000 : ℝ) (88705985929/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67069/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177411971851/1000000000000 : ℝ) (88705985929/500000000000 : ℝ) (23548239437/40000000000 : ℝ) (588705985929/1000000000000 : ℝ) (42120300551/100000000000 : ℝ) (421203005519/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67069/524288 : ℝ))) 1 (23548239437/40000000000 : ℝ) (588705985929/1000000000000 : ℝ) (42120300551/100000000000 : ℝ) (421203005519/1000000000000 : ℝ) (504954495717/1000000000000 : ℝ) (126238623931/250000000000 : ℝ) (124490142841/250000000000 : ℝ) (124490142843/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67069/524288 : ℝ))) 2 (504954495717/1000000000000 : ℝ) (126238623931/250000000000 : ℝ) (124490142841/250000000000 : ℝ) (124490142843/250000000000 : ℝ) (25072876677/50000000000 : ℝ) (125364383387/250000000000 : ℝ) (501445340191/1000000000000 : ℝ) (2507226701/5000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67069/524288 : ℝ))) 3 (25072876677/50000000000 : ℝ) (125364383387/250000000000 : ℝ) (501445340191/1000000000000 : ℝ) (2507226701/5000000000 : ℝ) (100290287373/200000000000 : ℝ) (250725718437/500000000000 : ℝ) (125362859207/250000000000 : ℝ) (501451436837/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67069/524288 : ℝ))) 4 (100290287373/200000000000 : ℝ) (250725718437/500000000000 : ℝ) (125362859207/250000000000 : ℝ) (501451436837/1000000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67069/524288 : ℝ))) 5 (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67069/524288 : ℝ))) 6 (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67069/524288 : ℝ))) 7 (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67069/524288 : ℝ)) hmem 8 (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67069/524288 : ℝ))) hcmem 8 (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67069/524288 : ℝ)) (62003280181/62500000000 : ℝ) (496026241449/500000000000 : ℝ) (250725718423/500000000000 : ℝ) (62681429607/125000000000 : ℝ) (396994155371/500000000000 : ℝ) (19849707769/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0996_exp_lower
  have heNumeric : (256862737213/125000000000 : ℝ)/4 ≤ Real.exp (-4262824016989/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862737213/125000000000 : ℝ)/4 ≤ Real.exp ((16767/131072 : ℝ)-(19849707769/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16767/131072 : ℝ) (67069/524288 : ℝ) (19849707769/25000000000 : ℝ) (256862737213/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0997; no trusted numerical premise.
theorem cover8_leaf0997_exp_radius : (15593799290489059/15625000000000000 : ℝ) ≤ Real.exp ((-33535/2097152 : ℝ)/8) ∧ Real.exp ((-33535/2097152 : ℝ)/8) ≤ (998003154591299777/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33535/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0997_exp_lower : (920113468468741729/1000000000000000000 : ℝ) ≤ Real.exp ((-85256480002163/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256480002163/128000000000000 : ℝ)/8) ≤ (92011346846874173/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256480002163/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0997_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725475781/250000000000 : ℝ) ≤ 4*Real.exp (67069/524288 : ℝ)*Real.exp (-mu (radius 8 (33535/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725475781/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33535/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0997_exp_radius
  have hrNumeric : (492068219461/500000000000 : ℝ) ≤ Real.exp (-33535/2097152 : ℝ) ∧ Real.exp (-33535/2097152 : ℝ) ≤ (984136438923/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492068219461/500000000000 : ℝ) ≤ (radius 8 (33535/262144 : ℝ)) ∧ (radius 8 (33535/262144 : ℝ)) ≤ (984136438923/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33535/262144 : ℝ)) (492068219461/500000000000 : ℝ) (984136438923/1000000000000 : ℝ) (35482654683/200000000000 : ℝ) (177413273421/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33535/262144 : ℝ)) (492068219461/500000000000 : ℝ) (984136438923/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33535/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492068219461/500000000000 : ℝ) (984136438923/1000000000000 : ℝ) (992068219461/1000000000000 : ℝ) (496034109731/500000000000 : ℝ) (992036510881/1000000000000 : ℝ) (992036510883/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33535/262144 : ℝ)) 1 (992068219461/1000000000000 : ℝ) (496034109731/500000000000 : ℝ) (992036510881/1000000000000 : ℝ) (992036510883/1000000000000 : ℝ) (992052365171/1000000000000 : ℝ) (992052365173/1000000000000 : ℝ) (248013091261/250000000000 : ℝ) (496026182523/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33535/262144 : ℝ)) 2 (992052365171/1000000000000 : ℝ) (992052365173/1000000000000 : ℝ) (248013091261/250000000000 : ℝ) (496026182523/500000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33535/262144 : ℝ)) 3 (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33535/262144 : ℝ)) 4 (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33535/262144 : ℝ)) 5 (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33535/262144 : ℝ)) 6 (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33535/262144 : ℝ)) 7 (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33535/262144 : ℝ))) (35482654683/200000000000 : ℝ) (177413273421/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33535/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35482654683/200000000000 : ℝ) (177413273421/1000000000000 : ℝ) (588706636707/1000000000000 : ℝ) (588706636711/1000000000000 : ℝ) (421204550563/1000000000000 : ℝ) (421204550571/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33535/262144 : ℝ))) 1 (588706636707/1000000000000 : ℝ) (588706636711/1000000000000 : ℝ) (421204550563/1000000000000 : ℝ) (421204550571/1000000000000 : ℝ) (100991118727/200000000000 : ℝ) (504955593641/1000000000000 : ℝ) (15561304997/31250000000 : ℝ) (62245219989/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33535/262144 : ℝ))) 2 (100991118727/200000000000 : ℝ) (504955593641/1000000000000 : ℝ) (15561304997/31250000000 : ℝ) (62245219989/125000000000 : ℝ) (501458676769/1000000000000 : ℝ) (501458676777/1000000000000 : ℝ) (125361620941/250000000000 : ℝ) (125361620943/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33535/262144 : ℝ))) 3 (501458676769/1000000000000 : ℝ) (501458676777/1000000000000 : ℝ) (125361620941/250000000000 : ℝ) (125361620943/250000000000 : ℝ) (250726290133/500000000000 : ℝ) (20058103211/40000000000 : ℝ) (501452580229/1000000000000 : ℝ) (250726290119/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33535/262144 : ℝ))) 4 (250726290133/500000000000 : ℝ) (20058103211/40000000000 : ℝ) (501452580229/1000000000000 : ℝ) (250726290119/500000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33535/262144 : ℝ))) 5 (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33535/262144 : ℝ))) 6 (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33535/262144 : ℝ))) 7 (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33535/262144 : ℝ)) hmem 8 (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33535/262144 : ℝ))) hcmem 8 (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33535/262144 : ℝ)) (992052365107/1000000000000 : ℝ) (99205236511/100000000000 : ℝ) (501452580247/1000000000000 : ℝ) (501452580257/1000000000000 : ℝ) (198497553863/250000000000 : ℝ) (793990215471/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0997_exp_lower
  have heNumeric : (513725475781/250000000000 : ℝ)/4 ≤ Real.exp (-85256480002163/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725475781/250000000000 : ℝ)/4 ≤ Real.exp ((67069/524288 : ℝ)-(793990215471/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67069/524288 : ℝ) (33535/262144 : ℝ) (793990215471/1000000000000 : ℝ) (513725475781/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0998; no trusted numerical premise.
theorem cover8_leaf0998_exp_radius : (499001562424244231/500000000000000000 : ℝ) ≤ Real.exp ((-67071/4194304 : ℝ)/8) ∧ Real.exp ((-67071/4194304 : ℝ)/8) ≤ (998003124848488463/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67071/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0998_exp_lower : (460056734387203599/500000000000000000 : ℝ) ≤ Real.exp ((-42628239830993/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628239830993/64000000000000 : ℝ)/8) ≤ (920113468774407199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628239830993/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0998_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980381717/200000000000 : ℝ) ≤ 4*Real.exp (33535/262144 : ℝ)*Real.exp (-mu (radius 8 (67071/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980381717/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (67071/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0998_exp_radius
  have hrNumeric : (492068102143/500000000000 : ℝ) ≤ Real.exp (-67071/4194304 : ℝ) ∧ Real.exp (-67071/4194304 : ℝ) ≤ (984136204287/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492068102143/500000000000 : ℝ) ≤ (radius 8 (67071/524288 : ℝ)) ∧ (radius 8 (67071/524288 : ℝ)) ≤ (984136204287/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (67071/524288 : ℝ)) (492068102143/500000000000 : ℝ) (984136204287/1000000000000 : ℝ) (177414574969/1000000000000 : ℝ) (7096582999/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (67071/524288 : ℝ)) (492068102143/500000000000 : ℝ) (984136204287/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (67071/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492068102143/500000000000 : ℝ) (984136204287/1000000000000 : ℝ) (992068102143/1000000000000 : ℝ) (484408253/488281250 : ℝ) (992036392621/1000000000000 : ℝ) (992036392623/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (67071/524288 : ℝ)) 1 (992068102143/1000000000000 : ℝ) (484408253/488281250 : ℝ) (992036392621/1000000000000 : ℝ) (992036392623/1000000000000 : ℝ) (496026123691/500000000000 : ℝ) (124006530923/125000000000 : ℝ) (198410449451/200000000000 : ℝ) (992052247257/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (67071/524288 : ℝ)) 2 (496026123691/500000000000 : ℝ) (124006530923/125000000000 : ℝ) (198410449451/200000000000 : ℝ) (992052247257/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (67071/524288 : ℝ)) 3 (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (67071/524288 : ℝ)) 4 (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (67071/524288 : ℝ)) 5 (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (67071/524288 : ℝ)) 6 (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (67071/524288 : ℝ)) 7 (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (67071/524288 : ℝ))) (177414574969/1000000000000 : ℝ) (7096582999/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (67071/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177414574969/1000000000000 : ℝ) (7096582999/40000000000 : ℝ) (147176821871/250000000000 : ℝ) (9198551367/15625000000 : ℝ) (210603047799/500000000000 : ℝ) (210603047803/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (67071/524288 : ℝ))) 1 (147176821871/250000000000 : ℝ) (9198551367/15625000000 : ℝ) (210603047799/500000000000 : ℝ) (210603047803/500000000000 : ℝ) (504956691541/1000000000000 : ℝ) (504956691547/1000000000000 : ℝ) (31122684277/62500000000 : ℝ) (497962948439/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (67071/524288 : ℝ))) 2 (504956691541/1000000000000 : ℝ) (504956691547/1000000000000 : ℝ) (31122684277/62500000000 : ℝ) (497962948439/1000000000000 : ℝ) (250729909993/500000000000 : ℝ) (501459819993/1000000000000 : ℝ) (20057905093/40000000000 : ℝ) (125361906833/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (67071/524288 : ℝ))) 3 (250729909993/500000000000 : ℝ) (501459819993/1000000000000 : ℝ) (20057905093/40000000000 : ℝ) (125361906833/250000000000 : ℝ) (100290744731/200000000000 : ℝ) (501453723663/1000000000000 : ℝ) (250726861809/500000000000 : ℝ) (250726861813/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (67071/524288 : ℝ))) 4 (100290744731/200000000000 : ℝ) (501453723663/1000000000000 : ℝ) (250726861809/500000000000 : ℝ) (250726861813/500000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (67071/524288 : ℝ))) 5 (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (67071/524288 : ℝ))) 6 (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (67071/524288 : ℝ))) 7 (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (67071/524288 : ℝ)) hmem 8 (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (67071/524288 : ℝ))) hcmem 8 (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (67071/524288 : ℝ)) (496026123659/500000000000 : ℝ) (992052247321/1000000000000 : ℝ) (125363430909/250000000000 : ℝ) (100290744729/200000000000 : ℝ) (158798424029/200000000000 : ℝ) (396996060081/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0998_exp_lower
  have heNumeric : (410980381717/200000000000 : ℝ)/4 ≤ Real.exp (-42628239830993/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980381717/200000000000 : ℝ)/4 ≤ Real.exp ((33535/262144 : ℝ)-(396996060081/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33535/262144 : ℝ) (67071/524288 : ℝ) (396996060081/500000000000 : ℝ) (410980381717/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0999; no trusted numerical premise.
theorem cover8_leaf0999_exp_radius : (499001547552839017/500000000000000000 : ℝ) ≤ Real.exp ((-131/8192 : ℝ)/8) ∧ Real.exp ((-131/8192 : ℝ)/8) ≤ (199600619021135607/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-131/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0999_exp_lower : (920113469080992779/1000000000000000000 : ℝ) ≤ Real.exp ((-17051295864157/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051295864157/25600000000000 : ℝ)/8) ≤ (46005673454049639/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051295864157/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0999_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901914063/1000000000000 : ℝ) ≤ 4*Real.exp (67071/524288 : ℝ)*Real.exp (-mu (radius 8 (131/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901914063/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (131/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0999_exp_radius
  have hrNumeric : (984135969649/1000000000000 : ℝ) ≤ Real.exp (-131/8192 : ℝ) ∧ Real.exp (-131/8192 : ℝ) ≤ (19682719393/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984135969649/1000000000000 : ℝ) ≤ (radius 8 (131/1024 : ℝ)) ∧ (radius 8 (131/1024 : ℝ)) ≤ (19682719393/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (131/1024 : ℝ)) (984135969649/1000000000000 : ℝ) (19682719393/20000000000 : ℝ) (177415876519/1000000000000 : ℝ) (7096635061/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (131/1024 : ℝ)) (984135969649/1000000000000 : ℝ) (19682719393/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (131/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984135969649/1000000000000 : ℝ) (19682719393/20000000000 : ℝ) (124008498103/125000000000 : ℝ) (39682719393/40000000000 : ℝ) (992036274361/1000000000000 : ℝ) (496018137181/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (131/1024 : ℝ)) 1 (124008498103/125000000000 : ℝ) (39682719393/40000000000 : ℝ) (992036274361/1000000000000 : ℝ) (496018137181/500000000000 : ℝ) (124006516199/125000000000 : ℝ) (496026064797/500000000000 : ℝ) (198410425893/200000000000 : ℝ) (992052129467/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (131/1024 : ℝ)) 2 (124006516199/125000000000 : ℝ) (496026064797/500000000000 : ℝ) (198410425893/200000000000 : ℝ) (992052129467/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (131/1024 : ℝ)) 3 (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (131/1024 : ℝ)) 4 (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (131/1024 : ℝ)) 5 (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (131/1024 : ℝ)) 6 (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (131/1024 : ℝ)) 7 (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (131/1024 : ℝ))) (177415876519/1000000000000 : ℝ) (7096635061/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (131/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177415876519/1000000000000 : ℝ) (7096635061/40000000000 : ℝ) (588707938259/1000000000000 : ℝ) (588707938263/1000000000000 : ℝ) (210603820311/500000000000 : ℝ) (42120764063/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (131/1024 : ℝ))) 1 (588707938259/1000000000000 : ℝ) (588707938263/1000000000000 : ℝ) (210603820311/500000000000 : ℝ) (42120764063/100000000000 : ℝ) (394498273/781250000 : ℝ) (504957789447/1000000000000 : ℝ) (497964136951/1000000000000 : ℝ) (248982068479/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (131/1024 : ℝ))) 2 (394498273/781250000 : ℝ) (504957789447/1000000000000 : ℝ) (497964136951/1000000000000 : ℝ) (248982068479/500000000000 : ℝ) (100292192639/200000000000 : ℝ) (501460963203/1000000000000 : ℝ) (250724385439/500000000000 : ℝ) (250724385443/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (131/1024 : ℝ))) 3 (100292192639/200000000000 : ℝ) (501460963203/1000000000000 : ℝ) (250724385439/500000000000 : ℝ) (250724385443/500000000000 : ℝ) (125363716759/250000000000 : ℝ) (100290973409/200000000000 : ℝ) (501454866999/1000000000000 : ℝ) (7835232297/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (131/1024 : ℝ))) 4 (125363716759/250000000000 : ℝ) (100290973409/200000000000 : ℝ) (501454866999/1000000000000 : ℝ) (7835232297/15625000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (131/1024 : ℝ))) 5 (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (131/1024 : ℝ))) 6 (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (131/1024 : ℝ))) 7 (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (131/1024 : ℝ)) hmem 8 (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (131/1024 : ℝ))) hcmem 8 (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (131/1024 : ℝ)) (124006516191/125000000000 : ℝ) (992052129531/1000000000000 : ℝ) (501454867017/1000000000000 : ℝ) (501454867027/1000000000000 : ℝ) (396997012413/500000000000 : ℝ) (158798804969/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0999_exp_lower
  have heNumeric : (2054901914063/1000000000000 : ℝ)/4 ≤ Real.exp (-17051295864157/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901914063/1000000000000 : ℝ)/4 ≤ Real.exp ((67071/524288 : ℝ)-(158798804969/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (67071/524288 : ℝ) (131/1024 : ℝ) (158798804969/200000000000 : ℝ) (2054901914063/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0975_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0975_certificate
#check SmaleRate.Proofs.cover8_leaf0976_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0976_certificate
#check SmaleRate.Proofs.cover8_leaf0977_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0977_certificate
#check SmaleRate.Proofs.cover8_leaf0978_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0978_certificate
#check SmaleRate.Proofs.cover8_leaf0979_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0979_certificate
#check SmaleRate.Proofs.cover8_leaf0980_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0980_certificate
#check SmaleRate.Proofs.cover8_leaf0981_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0981_certificate
#check SmaleRate.Proofs.cover8_leaf0982_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0982_certificate
#check SmaleRate.Proofs.cover8_leaf0983_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0983_certificate
#check SmaleRate.Proofs.cover8_leaf0984_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0984_certificate
#check SmaleRate.Proofs.cover8_leaf0985_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0985_certificate
#check SmaleRate.Proofs.cover8_leaf0986_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0986_certificate
#check SmaleRate.Proofs.cover8_leaf0987_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0987_certificate
#check SmaleRate.Proofs.cover8_leaf0988_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0988_certificate
#check SmaleRate.Proofs.cover8_leaf0989_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0989_certificate
#check SmaleRate.Proofs.cover8_leaf0990_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0990_certificate
#check SmaleRate.Proofs.cover8_leaf0991_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0991_certificate
#check SmaleRate.Proofs.cover8_leaf0992_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0992_certificate
#check SmaleRate.Proofs.cover8_leaf0993_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0993_certificate
#check SmaleRate.Proofs.cover8_leaf0994_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0994_certificate
#check SmaleRate.Proofs.cover8_leaf0995_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0995_certificate
#check SmaleRate.Proofs.cover8_leaf0996_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0996_certificate
#check SmaleRate.Proofs.cover8_leaf0997_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0997_certificate
#check SmaleRate.Proofs.cover8_leaf0998_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0998_certificate
#check SmaleRate.Proofs.cover8_leaf0999_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0999_certificate
