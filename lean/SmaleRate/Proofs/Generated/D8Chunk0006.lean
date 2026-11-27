/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0150; no trusted numerical premise.
theorem cover8_leaf0150_exp_radius : (124757287410969031/125000000000000000 : ℝ) ≤ Real.exp ((-1019/65536 : ℝ)/8) ∧ Real.exp ((-1019/65536 : ℝ)/8) ≤ (998058299287752249/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1019/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0150_exp_lower : (920113484138880751/1000000000000000000 : ℝ) ≤ Real.exp ((-5328528910173/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328528910173/8000000000000 : ℝ)/8) ≤ (57507092758680047/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328528910173/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0150_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980436619/200000000000 : ℝ) ≤ 4*Real.exp (4075/32768 : ℝ)*Real.exp (-mu (radius 8 (1019/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (410980436619/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1019/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0150_exp_radius
  have hrNumeric : (246142887747/250000000000 : ℝ) ≤ Real.exp (-1019/65536 : ℝ) ∧ Real.exp (-1019/65536 : ℝ) ≤ (984571550989/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246142887747/250000000000 : ℝ) ≤ (radius 8 (1019/8192 : ℝ)) ∧ (radius 8 (1019/8192 : ℝ)) ≤ (984571550989/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1019/8192 : ℝ)) (246142887747/250000000000 : ℝ) (984571550989/1000000000000 : ℝ) (2734100923/15625000000 : ℝ) (174982459079/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1019/8192 : ℝ)) (246142887747/250000000000 : ℝ) (984571550989/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1019/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246142887747/250000000000 : ℝ) (984571550989/1000000000000 : ℝ) (496142887747/500000000000 : ℝ) (198457155099/200000000000 : ℝ) (248063947273/250000000000 : ℝ) (496127894547/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1019/8192 : ℝ)) 1 (496142887747/500000000000 : ℝ) (198457155099/200000000000 : ℝ) (248063947273/250000000000 : ℝ) (496127894547/500000000000 : ℝ) (992270782293/1000000000000 : ℝ) (198454156459/200000000000 : ℝ) (992270782179/1000000000000 : ℝ) (496135391091/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1019/8192 : ℝ)) 2 (992270782293/1000000000000 : ℝ) (198454156459/200000000000 : ℝ) (992270782179/1000000000000 : ℝ) (496135391091/500000000000 : ℝ) (248067695559/250000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1019/8192 : ℝ)) 3 (248067695559/250000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1019/8192 : ℝ)) 4 (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1019/8192 : ℝ)) 5 (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1019/8192 : ℝ)) 6 (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1019/8192 : ℝ)) 7 (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1019/8192 : ℝ))) (2734100923/15625000000 : ℝ) (174982459079/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1019/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2734100923/15625000000 : ℝ) (174982459079/1000000000000 : ℝ) (18359100923/31250000000 : ℝ) (29374561477/50000000000 : ℝ) (209154523661/500000000000 : ℝ) (104577261833/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1019/8192 : ℝ))) 1 (18359100923/31250000000 : ℝ) (29374561477/50000000000 : ℝ) (209154523661/500000000000 : ℝ) (104577261833/250000000000 : ℝ) (502900138429/1000000000000 : ℝ) (125725034609/250000000000 : ℝ) (99146940757/200000000000 : ℝ) (247867351897/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1019/8192 : ℝ))) 2 (502900138429/1000000000000 : ℝ) (125725034609/250000000000 : ℝ) (99146940757/200000000000 : ℝ) (247867351897/500000000000 : ℝ) (499317421107/1000000000000 : ℝ) (99863484223/200000000000 : ℝ) (499304567531/1000000000000 : ℝ) (24965228377/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1019/8192 : ℝ))) 3 (499317421107/1000000000000 : ℝ) (99863484223/200000000000 : ℝ) (499304567531/1000000000000 : ℝ) (24965228377/50000000000 : ℝ) (499310994319/1000000000000 : ℝ) (62413874291/125000000000 : ℝ) (499310994277/1000000000000 : ℝ) (499310994287/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1019/8192 : ℝ))) 4 (499310994319/1000000000000 : ℝ) (62413874291/125000000000 : ℝ) (499310994277/1000000000000 : ℝ) (499310994287/1000000000000 : ℝ) (249655497149/500000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1019/8192 : ℝ))) 5 (249655497149/500000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1019/8192 : ℝ))) 6 (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1019/8192 : ℝ))) 7 (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1019/8192 : ℝ)) hmem 8 (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1019/8192 : ℝ))) hcmem 8 (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1019/8192 : ℝ)) (198454156447/200000000000 : ℝ) (992270782239/1000000000000 : ℝ) (499310994297/1000000000000 : ℝ) (124827748577/250000000000 : ℝ) (790425244609/1000000000000 : ℝ) (790425244631/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0150_exp_lower
  have heNumeric : (410980436619/200000000000 : ℝ)/4 ≤ Real.exp (-5328528910173/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980436619/200000000000 : ℝ)/4 ≤ Real.exp ((4075/32768 : ℝ)-(790425244631/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4075/32768 : ℝ) (1019/8192 : ℝ) (790425244631/1000000000000 : ℝ) (410980436619/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0151; no trusted numerical premise.
theorem cover8_leaf0151_exp_radius : (998057823376582561/1000000000000000000 : ℝ) ≤ Real.exp ((-4077/262144 : ℝ)/8) ∧ Real.exp ((-4077/262144 : ℝ)/8) ≤ (499028911688291281/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4077/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0151_exp_lower : (920113421952452333/1000000000000000000 : ℝ) ≤ Real.exp ((-1332133308913/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332133308913/2000000000000 : ℝ)/8) ≤ (460056710976226167/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332133308913/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0151_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372526801/25000000000 : ℝ) ≤ 4*Real.exp (1019/8192 : ℝ)*Real.exp (-mu (radius 8 (4077/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (51372526801/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4077/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0151_exp_radius
  have hrNumeric : (61535487197/62500000000 : ℝ) ≤ Real.exp (-4077/262144 : ℝ) ∧ Real.exp (-4077/262144 : ℝ) ≤ (984567795153/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61535487197/62500000000 : ℝ) ≤ (radius 8 (4077/32768 : ℝ)) ∧ (radius 8 (4077/32768 : ℝ)) ≤ (984567795153/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4077/32768 : ℝ)) (61535487197/62500000000 : ℝ) (984567795153/1000000000000 : ℝ) (17500359067/100000000000 : ℝ) (175003590677/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4077/32768 : ℝ)) (61535487197/62500000000 : ℝ) (984567795153/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4077/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61535487197/62500000000 : ℝ) (984567795153/1000000000000 : ℝ) (124035487197/125000000000 : ℝ) (992283897577/1000000000000 : ℝ) (248063474129/250000000000 : ℝ) (992253896517/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4077/32768 : ℝ)) 1 (124035487197/125000000000 : ℝ) (992283897577/1000000000000 : ℝ) (248063474129/250000000000 : ℝ) (992253896517/1000000000000 : ℝ) (496134448523/500000000000 : ℝ) (992268897047/1000000000000 : ℝ) (248067224233/250000000000 : ℝ) (496134448467/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4077/32768 : ℝ)) 2 (496134448523/500000000000 : ℝ) (992268897047/1000000000000 : ℝ) (248067224233/250000000000 : ℝ) (496134448467/500000000000 : ℝ) (992268896989/1000000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4077/32768 : ℝ)) 3 (992268896989/1000000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4077/32768 : ℝ)) 4 (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4077/32768 : ℝ)) 5 (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4077/32768 : ℝ)) 6 (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4077/32768 : ℝ)) 7 (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4077/32768 : ℝ))) (17500359067/100000000000 : ℝ) (175003590677/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4077/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17500359067/100000000000 : ℝ) (175003590677/1000000000000 : ℝ) (117500359067/200000000000 : ℝ) (587501795339/1000000000000 : ℝ) (104583576229/250000000000 : ℝ) (16733372197/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4077/32768 : ℝ))) 1 (117500359067/200000000000 : ℝ) (587501795339/1000000000000 : ℝ) (104583576229/250000000000 : ℝ) (16733372197/40000000000 : ℝ) (4023344401/8000000000 : ℝ) (125729512533/250000000000 : ℝ) (495754127757/1000000000000 : ℝ) (99150825553/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4077/32768 : ℝ))) 2 (4023344401/8000000000 : ℝ) (125729512533/250000000000 : ℝ) (495754127757/1000000000000 : ℝ) (99150825553/200000000000 : ℝ) (499336088941/1000000000000 : ℝ) (499336088949/1000000000000 : ℝ) (49932324127/100000000000 : ℝ) (499323241279/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4077/32768 : ℝ))) 3 (499336088941/1000000000000 : ℝ) (499336088949/1000000000000 : ℝ) (49932324127/100000000000 : ℝ) (499323241279/1000000000000 : ℝ) (99865933021/200000000000 : ℝ) (249664832557/500000000000 : ℝ) (62416208133/125000000000 : ℝ) (499329665073/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4077/32768 : ℝ))) 4 (99865933021/200000000000 : ℝ) (249664832557/500000000000 : ℝ) (62416208133/125000000000 : ℝ) (499329665073/1000000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4077/32768 : ℝ))) 5 (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4077/32768 : ℝ))) 6 (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4077/32768 : ℝ))) 7 (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4077/32768 : ℝ)) hmem 8 (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4077/32768 : ℝ))) hcmem 8 (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4077/32768 : ℝ)) (248067224247/250000000000 : ℝ) (992268896991/1000000000000 : ℝ) (124832416271/250000000000 : ℝ) (249664832547/500000000000 : ℝ) (6323650423/8000000000 : ℝ) (395228151447/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0151_exp_lower
  have heNumeric : (51372526801/25000000000 : ℝ)/4 ≤ Real.exp (-1332133308913/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372526801/25000000000 : ℝ)/4 ≤ Real.exp ((1019/8192 : ℝ)-(395228151447/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1019/8192 : ℝ) (4077/32768 : ℝ) (395228151447/500000000000 : ℝ) (51372526801/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0152; no trusted numerical premise.
theorem cover8_leaf0152_exp_radius : (998057585421082817/1000000000000000000 : ℝ) ≤ Real.exp ((-8155/524288 : ℝ)/8) ∧ Real.exp ((-8155/524288 : ℝ)/8) ≤ (499028792710541409/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8155/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0152_exp_lower : (920115146061691967/1000000000000000000 : ℝ) ≤ Real.exp ((-1065682662503/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065682662503/1600000000000 : ℝ)/8) ≤ (14376799157213937/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065682662503/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0152_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513732969011/250000000000 : ℝ) ≤ 4*Real.exp (4077/32768 : ℝ)*Real.exp (-mu (radius 8 (8155/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513732969011/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8155/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0152_exp_radius
  have hrNumeric : (24614147931/25000000000 : ℝ) ≤ Real.exp (-8155/524288 : ℝ) ∧ Real.exp (-8155/524288 : ℝ) ≤ (984565917241/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24614147931/25000000000 : ℝ) ≤ (radius 8 (8155/65536 : ℝ)) ∧ (radius 8 (8155/65536 : ℝ)) ≤ (984565917241/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8155/65536 : ℝ)) (24614147931/25000000000 : ℝ) (984565917241/1000000000000 : ℝ) (21876769431/125000000000 : ℝ) (35002831091/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8155/65536 : ℝ)) (24614147931/25000000000 : ℝ) (984565917241/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8155/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24614147931/25000000000 : ℝ) (984565917241/1000000000000 : ℝ) (49614147931/50000000000 : ℝ) (992282958621/1000000000000 : ℝ) (992252950229/1000000000000 : ℝ) (992252950231/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8155/65536 : ℝ)) 1 (49614147931/50000000000 : ℝ) (992282958621/1000000000000 : ℝ) (992252950229/1000000000000 : ℝ) (992252950231/1000000000000 : ℝ) (124033494303/125000000000 : ℝ) (496133977213/500000000000 : ℝ) (992267954311/1000000000000 : ℝ) (992267954313/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8155/65536 : ℝ)) 2 (124033494303/125000000000 : ℝ) (496133977213/500000000000 : ℝ) (992267954311/1000000000000 : ℝ) (992267954313/1000000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8155/65536 : ℝ)) 3 (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8155/65536 : ℝ)) 4 (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8155/65536 : ℝ)) 5 (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8155/65536 : ℝ)) 6 (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8155/65536 : ℝ)) 7 (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8155/65536 : ℝ))) (21876769431/125000000000 : ℝ) (35002831091/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8155/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21876769431/125000000000 : ℝ) (35002831091/200000000000 : ℝ) (146876769431/250000000000 : ℝ) (18359596179/31250000000 : ℝ) (418346931921/1000000000000 : ℝ) (41834693193/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8155/65536 : ℝ))) 1 (146876769431/250000000000 : ℝ) (18359596179/31250000000 : ℝ) (418346931921/1000000000000 : ℝ) (41834693193/100000000000 : ℝ) (251463502411/500000000000 : ℝ) (502927004829/1000000000000 : ℝ) (247881919191/500000000000 : ℝ) (49576383839/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8155/65536 : ℝ))) 2 (251463502411/500000000000 : ℝ) (502927004829/1000000000000 : ℝ) (247881919191/500000000000 : ℝ) (49576383839/100000000000 : ℝ) (249672710801/500000000000 : ℝ) (49934542161/100000000000 : ℝ) (249666288441/500000000000 : ℝ) (499332576891/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8155/65536 : ℝ))) 3 (249672710801/500000000000 : ℝ) (49934542161/100000000000 : ℝ) (249666288441/500000000000 : ℝ) (499332576891/1000000000000 : ℝ) (249669499621/500000000000 : ℝ) (499338999251/1000000000000 : ℝ) (624173749/1250000000 : ℝ) (49933899921/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8155/65536 : ℝ))) 4 (249669499621/500000000000 : ℝ) (499338999251/1000000000000 : ℝ) (624173749/1250000000 : ℝ) (49933899921/100000000000 : ℝ) (499338999221/1000000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8155/65536 : ℝ))) 5 (499338999221/1000000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8155/65536 : ℝ))) 6 (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8155/65536 : ℝ))) 7 (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8155/65536 : ℝ)) hmem 8 (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8155/65536 : ℝ))) hcmem 8 (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8155/65536 : ℝ)) (992267954367/1000000000000 : ℝ) (99226795437/100000000000 : ℝ) (24966949961/50000000000 : ℝ) (499338999231/1000000000000 : ℝ) (790471830059/1000000000000 : ℝ) (2470224469/3125000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0152_exp_lower
  have heNumeric : (513732969011/250000000000 : ℝ)/4 ≤ Real.exp (-1065682662503/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513732969011/250000000000 : ℝ)/4 ≤ Real.exp ((4077/32768 : ℝ)-(2470224469/3125000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4077/32768 : ℝ) (8155/65536 : ℝ) (2470224469/3125000000 : ℝ) (513732969011/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0153; no trusted numerical premise.
theorem cover8_leaf0153_exp_radius : (199611469493127961/200000000000000000 : ℝ) ≤ Real.exp ((-2039/131072 : ℝ)/8) ∧ Real.exp ((-2039/131072 : ℝ)/8) ≤ (499028673732819903/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2039/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0153_exp_lower : (920115115340780157/1000000000000000000 : ℝ) ≤ Real.exp ((-10656830898709/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656830898709/16000000000000 : ℝ)/8) ≤ (460057557670390079/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656830898709/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0153_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027465663581/500000000000 : ℝ) ≤ 4*Real.exp (8155/65536 : ℝ)*Real.exp (-mu (radius 8 (2039/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027465663581/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2039/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0153_exp_radius
  have hrNumeric : (984564039331/1000000000000 : ℝ) ≤ Real.exp (-2039/131072 : ℝ) ∧ Real.exp (-2039/131072 : ℝ) ≤ (246141009833/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984564039331/1000000000000 : ℝ) ≤ (radius 8 (2039/16384 : ℝ)) ∧ (radius 8 (2039/16384 : ℝ)) ≤ (246141009833/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2039/16384 : ℝ)) (984564039331/1000000000000 : ℝ) (246141009833/250000000000 : ℝ) (175024719551/1000000000000 : ℝ) (87512359779/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2039/16384 : ℝ)) (984564039331/1000000000000 : ℝ) (246141009833/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2039/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984564039331/1000000000000 : ℝ) (246141009833/250000000000 : ℝ) (198456403933/200000000000 : ℝ) (496141009833/500000000000 : ℝ) (124031500493/125000000000 : ℝ) (198450400789/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2039/16384 : ℝ)) 1 (198456403933/200000000000 : ℝ) (496141009833/500000000000 : ℝ) (124031500493/125000000000 : ℝ) (198450400789/200000000000 : ℝ) (248066752951/250000000000 : ℝ) (496133505903/500000000000 : ℝ) (992267011691/1000000000000 : ℝ) (992267011693/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2039/16384 : ℝ)) 2 (248066752951/250000000000 : ℝ) (496133505903/500000000000 : ℝ) (992267011691/1000000000000 : ℝ) (992267011693/1000000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2039/16384 : ℝ)) 3 (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2039/16384 : ℝ)) 4 (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2039/16384 : ℝ)) 5 (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2039/16384 : ℝ)) 6 (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2039/16384 : ℝ)) 7 (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2039/16384 : ℝ))) (175024719551/1000000000000 : ℝ) (87512359779/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2039/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175024719551/1000000000000 : ℝ) (87512359779/500000000000 : ℝ) (23500494391/40000000000 : ℝ) (587512359779/1000000000000 : ℝ) (209179778869/500000000000 : ℝ) (418359557747/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2039/16384 : ℝ))) 1 (23500494391/40000000000 : ℝ) (587512359779/1000000000000 : ℝ) (209179778869/500000000000 : ℝ) (418359557747/1000000000000 : ℝ) (125733989689/250000000000 : ℝ) (502935958763/1000000000000 : ℝ) (99154709621/200000000000 : ℝ) (495773548113/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2039/16384 : ℝ))) 2 (125733989689/250000000000 : ℝ) (502935958763/1000000000000 : ℝ) (99154709621/200000000000 : ℝ) (495773548113/1000000000000 : ℝ) (49935475343/100000000000 : ℝ) (249677376719/500000000000 : ℝ) (499341911661/1000000000000 : ℝ) (49934191167/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2039/16384 : ℝ))) 3 (49935475343/100000000000 : ℝ) (249677376719/500000000000 : ℝ) (499341911661/1000000000000 : ℝ) (49934191167/100000000000 : ℝ) (99869666509/200000000000 : ℝ) (249674166277/500000000000 : ℝ) (62418541563/125000000000 : ℝ) (499348332513/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2039/16384 : ℝ))) 4 (99869666509/200000000000 : ℝ) (249674166277/500000000000 : ℝ) (62418541563/125000000000 : ℝ) (499348332513/1000000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2039/16384 : ℝ))) 5 (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2039/16384 : ℝ))) 6 (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2039/16384 : ℝ))) 7 (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2039/16384 : ℝ)) hmem 8 (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2039/16384 : ℝ))) hcmem 8 (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2039/16384 : ℝ)) (992267011747/1000000000000 : ℝ) (3969068047/4000000000 : ℝ) (124837083131/250000000000 : ℝ) (249674166267/500000000000 : ℝ) (158097471191/200000000000 : ℝ) (395243677987/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0153_exp_lower
  have heNumeric : (1027465663581/500000000000 : ℝ)/4 ≤ Real.exp (-10656830898709/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027465663581/500000000000 : ℝ)/4 ≤ Real.exp ((8155/65536 : ℝ)-(395243677987/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8155/65536 : ℝ) (2039/16384 : ℝ) (395243677987/500000000000 : ℝ) (1027465663581/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0154; no trusted numerical premise.
theorem cover8_leaf0154_exp_radius : (998057109510253527/1000000000000000000 : ℝ) ≤ Real.exp ((-8157/524288 : ℝ)/8) ∧ Real.exp ((-8157/524288 : ℝ)/8) ≤ (124757138688781691/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8157/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0154_exp_lower : (460057542384291487/500000000000000000 : ℝ) ≤ Real.exp ((-106568351517/160000000000 : ℝ)/8) ∧ Real.exp ((-106568351517/160000000000 : ℝ)/8) ≤ (36804603390743319/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-106568351517/160000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0154_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054930780937/1000000000000 : ℝ) ≤ 4*Real.exp (2039/16384 : ℝ)*Real.exp (-mu (radius 8 (8157/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054930780937/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8157/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0154_exp_radius
  have hrNumeric : (492281080713/500000000000 : ℝ) ≤ Real.exp (-8157/524288 : ℝ) ∧ Real.exp (-8157/524288 : ℝ) ≤ (984562161427/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492281080713/500000000000 : ℝ) ≤ (radius 8 (8157/65536 : ℝ)) ∧ (radius 8 (8157/65536 : ℝ)) ≤ (984562161427/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8157/65536 : ℝ)) (492281080713/500000000000 : ℝ) (984562161427/1000000000000 : ℝ) (7001411319/40000000000 : ℝ) (175035282981/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8157/65536 : ℝ)) (492281080713/500000000000 : ℝ) (984562161427/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8157/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492281080713/500000000000 : ℝ) (984562161427/1000000000000 : ℝ) (992281080713/1000000000000 : ℝ) (496140540357/500000000000 : ℝ) (992251057659/1000000000000 : ℝ) (49612552883/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8157/65536 : ℝ)) 1 (992281080713/1000000000000 : ℝ) (496140540357/500000000000 : ℝ) (992251057659/1000000000000 : ℝ) (49612552883/50000000000 : ℝ) (496133034593/500000000000 : ℝ) (992266069187/1000000000000 : ℝ) (62016629317/62500000000 : ℝ) (496133034537/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8157/65536 : ℝ)) 2 (496133034593/500000000000 : ℝ) (992266069187/1000000000000 : ℝ) (62016629317/62500000000 : ℝ) (496133034537/500000000000 : ℝ) (992266069129/1000000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8157/65536 : ℝ)) 3 (992266069129/1000000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8157/65536 : ℝ)) 4 (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8157/65536 : ℝ)) 5 (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8157/65536 : ℝ)) 6 (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8157/65536 : ℝ)) 7 (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8157/65536 : ℝ))) (7001411319/40000000000 : ℝ) (175035282981/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8157/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7001411319/40000000000 : ℝ) (175035282981/1000000000000 : ℝ) (587517641487/1000000000000 : ℝ) (587517641491/1000000000000 : ℝ) (209186091181/500000000000 : ℝ) (41837218237/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8157/65536 : ℝ))) 1 (587517641487/1000000000000 : ℝ) (587517641491/1000000000000 : ℝ) (209186091181/500000000000 : ℝ) (41837218237/100000000000 : ℝ) (125736227981/250000000000 : ℝ) (502944911931/1000000000000 : ℝ) (247891628461/500000000000 : ℝ) (49578325693/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8157/65536 : ℝ))) 2 (125736227981/250000000000 : ℝ) (502944911931/1000000000000 : ℝ) (247891628461/500000000000 : ℝ) (49578325693/100000000000 : ℝ) (499364084423/1000000000000 : ℝ) (499364084431/1000000000000 : ℝ) (499351245603/1000000000000 : ℝ) (124837811403/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8157/65536 : ℝ))) 3 (499364084423/1000000000000 : ℝ) (499364084431/1000000000000 : ℝ) (499351245603/1000000000000 : ℝ) (124837811403/250000000000 : ℝ) (499357665013/1000000000000 : ℝ) (249678832511/500000000000 : ℝ) (499357664971/1000000000000 : ℝ) (499357664981/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8157/65536 : ℝ))) 4 (499357665013/1000000000000 : ℝ) (249678832511/500000000000 : ℝ) (499357664971/1000000000000 : ℝ) (499357664981/1000000000000 : ℝ) (15604927031/31250000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8157/65536 : ℝ))) 5 (15604927031/31250000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8157/65536 : ℝ))) 6 (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8157/65536 : ℝ))) 7 (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8157/65536 : ℝ)) hmem 8 (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8157/65536 : ℝ))) hcmem 8 (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8157/65536 : ℝ)) (124033258641/125000000000 : ℝ) (992266069131/1000000000000 : ℝ) (499357664991/1000000000000 : ℝ) (249678832501/500000000000 : ℝ) (395251440277/500000000000 : ℝ) (31620115223/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0154_exp_lower
  have heNumeric : (2054930780937/1000000000000 : ℝ)/4 ≤ Real.exp (-106568351517/160000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054930780937/1000000000000 : ℝ)/4 ≤ Real.exp ((2039/16384 : ℝ)-(31620115223/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2039/16384 : ℝ) (8157/65536 : ℝ) (31620115223/40000000000 : ℝ) (2054930780937/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0155; no trusted numerical premise.
theorem cover8_leaf0155_exp_radius : (499028435777461991/500000000000000000 : ℝ) ≤ Real.exp ((-4079/262144 : ℝ)/8) ∧ Real.exp ((-4079/262144 : ℝ)/8) ≤ (998056871554923983/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4079/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0155_exp_lower : (115014381793223811/125000000000000000 : ℝ) ≤ Real.exp ((-10656839383907/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656839383907/16000000000000 : ℝ)/8) ≤ (920115054345790489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656839383907/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0155_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054930237381/1000000000000 : ℝ) ≤ 4*Real.exp (8157/65536 : ℝ)*Real.exp (-mu (radius 8 (4079/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054930237381/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4079/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0155_exp_radius
  have hrNumeric : (39382411341/40000000000 : ℝ) ≤ Real.exp (-4079/262144 : ℝ) ∧ Real.exp (-4079/262144 : ℝ) ≤ (492280141763/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39382411341/40000000000 : ℝ) ≤ (radius 8 (4079/32768 : ℝ)) ∧ (radius 8 (4079/32768 : ℝ)) ≤ (492280141763/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4079/32768 : ℝ)) (39382411341/40000000000 : ℝ) (492280141763/500000000000 : ℝ) (87522922859/500000000000 : ℝ) (43761461431/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4079/32768 : ℝ)) (39382411341/40000000000 : ℝ) (492280141763/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4079/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39382411341/40000000000 : ℝ) (492280141763/500000000000 : ℝ) (496140070881/500000000000 : ℝ) (992280141763/1000000000000 : ℝ) (7938000891/8000000000 : ℝ) (992250111377/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4079/32768 : ℝ)) 1 (496140070881/500000000000 : ℝ) (992280141763/1000000000000 : ℝ) (7938000891/8000000000 : ℝ) (992250111377/1000000000000 : ℝ) (124033140821/125000000000 : ℝ) (99226512657/100000000000 : ℝ) (496132563227/500000000000 : ℝ) (992265126457/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4079/32768 : ℝ)) 2 (124033140821/125000000000 : ℝ) (99226512657/100000000000 : ℝ) (496132563227/500000000000 : ℝ) (992265126457/1000000000000 : ℝ) (992265126511/1000000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4079/32768 : ℝ)) 3 (992265126511/1000000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4079/32768 : ℝ)) 4 (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4079/32768 : ℝ)) 5 (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4079/32768 : ℝ)) 6 (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4079/32768 : ℝ)) 7 (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4079/32768 : ℝ))) (87522922859/500000000000 : ℝ) (43761461431/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4079/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87522922859/500000000000 : ℝ) (43761461431/250000000000 : ℝ) (587522922859/1000000000000 : ℝ) (293761461431/500000000000 : ℝ) (13074525181/31250000000 : ℝ) (2091924029/5000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4079/32768 : ℝ))) 1 (587522922859/1000000000000 : ℝ) (293761461431/500000000000 : ℝ) (13074525181/31250000000 : ℝ) (2091924029/5000000000 : ℝ) (20118154573/40000000000 : ℝ) (502953864331/1000000000000 : ℝ) (495792964833/1000000000000 : ℝ) (12394824121/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4079/32768 : ℝ))) 2 (20118154573/40000000000 : ℝ) (502953864331/1000000000000 : ℝ) (495792964833/1000000000000 : ℝ) (12394824121/25000000000 : ℝ) (499373414579/1000000000000 : ℝ) (249686707293/500000000000 : ℝ) (124840144677/250000000000 : ℝ) (99872115743/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4079/32768 : ℝ))) 3 (499373414579/1000000000000 : ℝ) (249686707293/500000000000 : ℝ) (124840144677/250000000000 : ℝ) (99872115743/200000000000 : ℝ) (499366996643/1000000000000 : ℝ) (499366996651/1000000000000 : ℝ) (249683498301/500000000000 : ℝ) (49936699661/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4079/32768 : ℝ))) 4 (499366996643/1000000000000 : ℝ) (499366996651/1000000000000 : ℝ) (249683498301/500000000000 : ℝ) (49936699661/100000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4079/32768 : ℝ))) 5 (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4079/32768 : ℝ))) 6 (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4079/32768 : ℝ))) 7 (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4079/32768 : ℝ)) hmem 8 (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4079/32768 : ℝ))) hcmem 8 (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4079/32768 : ℝ)) (99226512651/100000000000 : ℝ) (496132563257/500000000000 : ℝ) (249683498311/500000000000 : ℝ) (499366996631/1000000000000 : ℝ) (395259201929/500000000000 : ℝ) (790518403877/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0155_exp_lower
  have heNumeric : (2054930237381/1000000000000 : ℝ)/4 ≤ Real.exp (-10656839383907/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054930237381/1000000000000 : ℝ)/4 ≤ Real.exp ((8157/65536 : ℝ)-(790518403877/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8157/65536 : ℝ) (4079/32768 : ℝ) (790518403877/1000000000000 : ℝ) (2054930237381/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0156; no trusted numerical premise.
theorem cover8_leaf0156_exp_radius : (99805663359965117/100000000000000000 : ℝ) ≤ Real.exp ((-8159/524288 : ℝ)/8) ∧ Real.exp ((-8159/524288 : ℝ)/8) ≤ (998056633599651171/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8159/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0156_exp_lower : (920115024071022513/1000000000000000000 : ℝ) ≤ Real.exp ((-5328421797761/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328421797761/8000000000000 : ℝ)/8) ≤ (460057512035511257/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328421797761/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0156_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205492969647/100000000000 : ℝ) ≤ 4*Real.exp (4079/32768 : ℝ)*Real.exp (-mu (radius 8 (8159/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205492969647/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8159/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0156_exp_radius
  have hrNumeric : (984558405627/1000000000000 : ℝ) ≤ Real.exp (-8159/524288 : ℝ) ∧ Real.exp (-8159/524288 : ℝ) ≤ (246139601407/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984558405627/1000000000000 : ℝ) ≤ (radius 8 (8159/65536 : ℝ)) ∧ (radius 8 (8159/65536 : ℝ)) ≤ (246139601407/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8159/65536 : ℝ)) (984558405627/1000000000000 : ℝ) (246139601407/250000000000 : ℝ) (87528203893/500000000000 : ℝ) (175056407793/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8159/65536 : ℝ)) (984558405627/1000000000000 : ℝ) (246139601407/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8159/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984558405627/1000000000000 : ℝ) (246139601407/250000000000 : ℝ) (992279202813/1000000000000 : ℝ) (496139601407/500000000000 : ℝ) (248062291273/250000000000 : ℝ) (496124582547/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8159/65536 : ℝ)) 1 (992279202813/1000000000000 : ℝ) (496139601407/500000000000 : ℝ) (248062291273/250000000000 : ℝ) (496124582547/500000000000 : ℝ) (62016511497/62500000000 : ℝ) (496132091977/500000000000 : ℝ) (496132091919/500000000000 : ℝ) (992264183841/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8159/65536 : ℝ)) 2 (62016511497/62500000000 : ℝ) (496132091977/500000000000 : ℝ) (496132091919/500000000000 : ℝ) (992264183841/1000000000000 : ℝ) (198452836779/200000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8159/65536 : ℝ)) 3 (198452836779/200000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8159/65536 : ℝ)) 4 (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8159/65536 : ℝ)) 5 (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8159/65536 : ℝ)) 6 (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8159/65536 : ℝ)) 7 (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8159/65536 : ℝ))) (87528203893/500000000000 : ℝ) (175056407793/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8159/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87528203893/500000000000 : ℝ) (175056407793/1000000000000 : ℝ) (587528203893/1000000000000 : ℝ) (587528203897/1000000000000 : ℝ) (209198714017/500000000000 : ℝ) (104599357011/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8159/65536 : ℝ))) 1 (587528203893/1000000000000 : ℝ) (587528203897/1000000000000 : ℝ) (209198714017/500000000000 : ℝ) (104599357011/250000000000 : ℝ) (502962815963/1000000000000 : ℝ) (502962815971/1000000000000 : ℝ) (247901335921/500000000000 : ℝ) (495802671851/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8159/65536 : ℝ))) 2 (502962815963/1000000000000 : ℝ) (502962815971/1000000000000 : ℝ) (247901335921/500000000000 : ℝ) (495802671851/1000000000000 : ℝ) (249691371951/500000000000 : ℝ) (499382743911/1000000000000 : ℝ) (499369910979/1000000000000 : ℝ) (124842477747/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8159/65536 : ℝ))) 3 (249691371951/500000000000 : ℝ) (499382743911/1000000000000 : ℝ) (499369910979/1000000000000 : ℝ) (124842477747/250000000000 : ℝ) (6242204093/12500000000 : ℝ) (9987526549/20000000000 : ℝ) (499376327399/1000000000000 : ℝ) (499376327409/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8159/65536 : ℝ))) 4 (6242204093/12500000000 : ℝ) (9987526549/20000000000 : ℝ) (499376327399/1000000000000 : ℝ) (499376327409/1000000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8159/65536 : ℝ))) 5 (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8159/65536 : ℝ))) 6 (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8159/65536 : ℝ))) 7 (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8159/65536 : ℝ)) hmem 8 (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8159/65536 : ℝ))) hcmem 8 (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8159/65536 : ℝ)) (496132091947/500000000000 : ℝ) (496132091949/500000000000 : ℝ) (499376327419/1000000000000 : ℝ) (49937632743/100000000000 : ℝ) (790533925871/1000000000000 : ℝ) (197633481473/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0156_exp_lower
  have heNumeric : (205492969647/100000000000 : ℝ)/4 ≤ Real.exp (-5328421797761/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205492969647/100000000000 : ℝ)/4 ≤ Real.exp ((4079/32768 : ℝ)-(197633481473/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4079/32768 : ℝ) (8159/65536 : ℝ) (197633481473/250000000000 : ℝ) (205492969647/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0157; no trusted numerical premise.
theorem cover8_leaf0157_exp_radius : (998056395644435091/1000000000000000000 : ℝ) ≤ Real.exp ((-255/16384 : ℝ)/8) ∧ Real.exp ((-255/16384 : ℝ)/8) ≤ (249514098911108773/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-255/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0157_exp_lower : (46005749697288711/50000000000000000 : ℝ) ≤ Real.exp ((-10656847786337/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656847786337/16000000000000 : ℝ)/8) ≤ (920114993945774221/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656847786337/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0157_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054929158231/1000000000000 : ℝ) ≤ 4*Real.exp (8159/65536 : ℝ)*Real.exp (-mu (radius 8 (255/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2054929158231/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (255/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0157_exp_radius
  have hrNumeric : (984556527733/1000000000000 : ℝ) ≤ Real.exp (-255/16384 : ℝ) ∧ Real.exp (-255/16384 : ℝ) ≤ (492278263867/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984556527733/1000000000000 : ℝ) ≤ (radius 8 (255/2048 : ℝ)) ∧ (radius 8 (255/2048 : ℝ)) ≤ (492278263867/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (255/2048 : ℝ)) (984556527733/1000000000000 : ℝ) (492278263867/500000000000 : ℝ) (7002678767/40000000000 : ℝ) (87533484591/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (255/2048 : ℝ)) (984556527733/1000000000000 : ℝ) (492278263867/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (255/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984556527733/1000000000000 : ℝ) (492278263867/500000000000 : ℝ) (496139131933/500000000000 : ℝ) (992278263867/1000000000000 : ℝ) (99224821881/100000000000 : ℝ) (248062054703/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (255/2048 : ℝ)) 1 (496139131933/500000000000 : ℝ) (992278263867/1000000000000 : ℝ) (99224821881/100000000000 : ℝ) (248062054703/250000000000 : ℝ) (496131620669/500000000000 : ℝ) (49613162067/50000000000 : ℝ) (124032905153/125000000000 : ℝ) (496131620613/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (255/2048 : ℝ)) 2 (496131620669/500000000000 : ℝ) (49613162067/50000000000 : ℝ) (124032905153/125000000000 : ℝ) (496131620613/500000000000 : ℝ) (992263241281/1000000000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (255/2048 : ℝ)) 3 (992263241281/1000000000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (255/2048 : ℝ)) 4 (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (255/2048 : ℝ)) 5 (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (255/2048 : ℝ)) 6 (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (255/2048 : ℝ)) 7 (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (255/2048 : ℝ))) (7002678767/40000000000 : ℝ) (87533484591/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (255/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7002678767/40000000000 : ℝ) (87533484591/500000000000 : ℝ) (587533484587/1000000000000 : ℝ) (587533484591/1000000000000 : ℝ) (104602512271/250000000000 : ℝ) (418410049093/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (255/2048 : ℝ))) 1 (587533484587/1000000000000 : ℝ) (587533484591/1000000000000 : ℝ) (104602512271/250000000000 : ℝ) (418410049093/1000000000000 : ℝ) (100594353367/200000000000 : ℝ) (251485883421/500000000000 : ℝ) (247906188973/500000000000 : ℝ) (247906188977/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (255/2048 : ℝ))) 2 (100594353367/200000000000 : ℝ) (251485883421/500000000000 : ℝ) (247906188973/500000000000 : ℝ) (247906188977/500000000000 : ℝ) (49939207239/100000000000 : ℝ) (249696036199/500000000000 : ℝ) (249689621207/500000000000 : ℝ) (249689621211/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (255/2048 : ℝ))) 3 (49939207239/100000000000 : ℝ) (249696036199/500000000000 : ℝ) (249689621207/500000000000 : ℝ) (249689621211/500000000000 : ℝ) (249692828701/500000000000 : ℝ) (49938565741/100000000000 : ℝ) (6242320717/12500000000 : ℝ) (499385657369/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (255/2048 : ℝ))) 4 (249692828701/500000000000 : ℝ) (49938565741/100000000000 : ℝ) (6242320717/12500000000 : ℝ) (499385657369/1000000000000 : ℝ) (499385657381/1000000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (255/2048 : ℝ))) 5 (499385657381/1000000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (255/2048 : ℝ))) 6 (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (255/2048 : ℝ))) 7 (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (255/2048 : ℝ)) hmem 8 (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (255/2048 : ℝ))) hcmem 8 (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (255/2048 : ℝ)) (3100822629/3125000000 : ℝ) (992263241283/1000000000000 : ℝ) (24969282869/50000000000 : ℝ) (49938565739/100000000000 : ℝ) (197637361647/250000000000 : ℝ) (790549446607/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0157_exp_lower
  have heNumeric : (2054929158231/1000000000000 : ℝ)/4 ≤ Real.exp (-10656847786337/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054929158231/1000000000000 : ℝ)/4 ≤ Real.exp ((8159/65536 : ℝ)-(790549446607/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8159/65536 : ℝ) (255/2048 : ℝ) (790549446607/1000000000000 : ℝ) (2054929158231/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0158; no trusted numerical premise.
theorem cover8_leaf0158_exp_radius : (31189254927789867/31250000000000000 : ℝ) ≤ Real.exp ((-8161/524288 : ℝ)/8) ∧ Real.exp ((-8161/524288 : ℝ)/8) ≤ (199611231537855149/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8161/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0158_exp_lower : (920114963968320379/1000000000000000000 : ℝ) ≤ Real.exp ((-666053247287/1000000000000 : ℝ)/8) ∧ Real.exp ((-666053247287/1000000000000 : ℝ)/8) ≤ (46005748198416019/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666053247287/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0158_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256866077829/125000000000 : ℝ) ≤ 4*Real.exp (255/2048 : ℝ)*Real.exp (-mu (radius 8 (8161/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (256866077829/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8161/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0158_exp_radius
  have hrNumeric : (492277324921/500000000000 : ℝ) ≤ Real.exp (-8161/524288 : ℝ) ∧ Real.exp (-8161/524288 : ℝ) ≤ (984554649843/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492277324921/500000000000 : ℝ) ≤ (radius 8 (8161/65536 : ℝ)) ∧ (radius 8 (8161/65536 : ℝ)) ≤ (984554649843/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8161/65536 : ℝ)) (492277324921/500000000000 : ℝ) (984554649843/1000000000000 : ℝ) (17507752989/100000000000 : ℝ) (175077529897/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8161/65536 : ℝ)) (492277324921/500000000000 : ℝ) (984554649843/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8161/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492277324921/500000000000 : ℝ) (984554649843/1000000000000 : ℝ) (992277324921/1000000000000 : ℝ) (496138662461/500000000000 : ℝ) (992247272529/1000000000000 : ℝ) (99224727253/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8161/65536 : ℝ)) 1 (992277324921/1000000000000 : ℝ) (496138662461/500000000000 : ℝ) (992247272529/1000000000000 : ℝ) (99224727253/100000000000 : ℝ) (39690491949/40000000000 : ℝ) (496131149363/500000000000 : ℝ) (992262298611/1000000000000 : ℝ) (992262298613/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8161/65536 : ℝ)) 2 (39690491949/40000000000 : ℝ) (496131149363/500000000000 : ℝ) (992262298611/1000000000000 : ℝ) (992262298613/1000000000000 : ℝ) (248065574667/250000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8161/65536 : ℝ)) 3 (248065574667/250000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8161/65536 : ℝ)) 4 (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8161/65536 : ℝ)) 5 (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8161/65536 : ℝ)) 6 (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8161/65536 : ℝ)) 7 (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8161/65536 : ℝ))) (17507752989/100000000000 : ℝ) (175077529897/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8161/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17507752989/100000000000 : ℝ) (175077529897/1000000000000 : ℝ) (117507752989/200000000000 : ℝ) (587538764949/1000000000000 : ℝ) (104605667237/250000000000 : ℝ) (418422668957/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8161/65536 : ℝ))) 1 (117507752989/200000000000 : ℝ) (587538764949/1000000000000 : ℝ) (104605667237/250000000000 : ℝ) (418422668957/1000000000000 : ℝ) (251490358473/500000000000 : ℝ) (502980716953/1000000000000 : ℝ) (495822083149/1000000000000 : ℝ) (495822083157/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8161/65536 : ℝ))) 2 (251490358473/500000000000 : ℝ) (502980716953/1000000000000 : ℝ) (495822083149/1000000000000 : ℝ) (495822083157/1000000000000 : ℝ) (499401400047/1000000000000 : ℝ) (99880280011/200000000000 : ℝ) (62423571627/125000000000 : ℝ) (19975542921/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8161/65536 : ℝ))) 3 (499401400047/1000000000000 : ℝ) (99880280011/200000000000 : ℝ) (62423571627/125000000000 : ℝ) (19975542921/40000000000 : ℝ) (499394986531/1000000000000 : ℝ) (24969749327/50000000000 : ℝ) (49939498649/100000000000 : ℝ) (499394986499/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8161/65536 : ℝ))) 4 (499394986531/1000000000000 : ℝ) (24969749327/50000000000 : ℝ) (49939498649/100000000000 : ℝ) (499394986499/1000000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8161/65536 : ℝ))) 5 (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8161/65536 : ℝ))) 6 (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8161/65536 : ℝ))) 7 (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8161/65536 : ℝ)) hmem 8 (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8161/65536 : ℝ))) hcmem 8 (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8161/65536 : ℝ)) (992262298667/1000000000000 : ℝ) (99226229867/100000000000 : ℝ) (49939498651/100000000000 : ℝ) (12484874663/25000000000 : ℝ) (395282483009/500000000000 : ℝ) (790564966037/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0158_exp_lower
  have heNumeric : (256866077829/125000000000 : ℝ)/4 ≤ Real.exp (-666053247287/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256866077829/125000000000 : ℝ)/4 ≤ Real.exp ((255/2048 : ℝ)-(790564966037/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (255/2048 : ℝ) (8161/65536 : ℝ) (790564966037/1000000000000 : ℝ) (256866077829/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0159; no trusted numerical premise.
theorem cover8_leaf0159_exp_radius : (998055919734173131/1000000000000000000 : ℝ) ≤ Real.exp ((-4081/262144 : ℝ)/8) ∧ Real.exp ((-4081/262144 : ℝ)/8) ≤ (249513979933543283/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4081/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0159_exp_lower : (184022986827985227/200000000000000000 : ℝ) ≤ Real.exp ((-10656856106111/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656856106111/16000000000000 : ℝ)/8) ≤ (115014366767490767/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656856106111/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0159_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054928089697/1000000000000 : ℝ) ≤ 4*Real.exp (8161/65536 : ℝ)*Real.exp (-mu (radius 8 (4081/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054928089697/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4081/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0159_exp_radius
  have hrNumeric : (196910554391/200000000000 : ℝ) ≤ Real.exp (-4081/262144 : ℝ) ∧ Real.exp (-4081/262144 : ℝ) ≤ (246138192989/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196910554391/200000000000 : ℝ) ≤ (radius 8 (4081/32768 : ℝ)) ∧ (radius 8 (4081/32768 : ℝ)) ≤ (246138192989/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4081/32768 : ℝ)) (196910554391/200000000000 : ℝ) (246138192989/250000000000 : ℝ) (7003523597/40000000000 : ℝ) (43772022483/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4081/32768 : ℝ)) (196910554391/200000000000 : ℝ) (246138192989/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4081/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196910554391/200000000000 : ℝ) (246138192989/250000000000 : ℝ) (992276385977/1000000000000 : ℝ) (496138192989/500000000000 : ℝ) (992246326249/1000000000000 : ℝ) (793797061/800000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4081/32768 : ℝ)) 1 (992276385977/1000000000000 : ℝ) (496138192989/500000000000 : ℝ) (992246326249/1000000000000 : ℝ) (793797061/800000000 : ℝ) (992261356113/1000000000000 : ℝ) (496130678057/500000000000 : ℝ) (992261355999/1000000000000 : ℝ) (992261356001/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4081/32768 : ℝ)) 2 (992261356113/1000000000000 : ℝ) (496130678057/500000000000 : ℝ) (992261355999/1000000000000 : ℝ) (992261356001/1000000000000 : ℝ) (124032669507/125000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4081/32768 : ℝ)) 3 (124032669507/125000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4081/32768 : ℝ)) 4 (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4081/32768 : ℝ)) 5 (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4081/32768 : ℝ)) 6 (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4081/32768 : ℝ)) 7 (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4081/32768 : ℝ))) (7003523597/40000000000 : ℝ) (43772022483/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4081/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7003523597/40000000000 : ℝ) (43772022483/250000000000 : ℝ) (293772022481/500000000000 : ℝ) (293772022483/500000000000 : ℝ) (418435287619/1000000000000 : ℝ) (104608821907/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4081/32768 : ℝ))) 1 (293772022481/500000000000 : ℝ) (293772022483/500000000000 : ℝ) (418435287619/1000000000000 : ℝ) (104608821907/250000000000 : ℝ) (50298966629/100000000000 : ℝ) (502989666297/1000000000000 : ℝ) (247915893723/500000000000 : ℝ) (247915893727/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4081/32768 : ℝ))) 2 (50298966629/100000000000 : ℝ) (502989666297/1000000000000 : ℝ) (247915893723/500000000000 : ℝ) (247915893727/500000000000 : ℝ) (124852681717/250000000000 : ℝ) (124852681719/250000000000 : ℝ) (249698951391/500000000000 : ℝ) (49939790279/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4081/32768 : ℝ))) 3 (124852681717/250000000000 : ℝ) (124852681719/250000000000 : ℝ) (249698951391/500000000000 : ℝ) (49939790279/100000000000 : ℝ) (19976172593/40000000000 : ℝ) (499404314833/1000000000000 : ℝ) (499404314783/1000000000000 : ℝ) (62425539349/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4081/32768 : ℝ))) 4 (19976172593/40000000000 : ℝ) (499404314833/1000000000000 : ℝ) (499404314783/1000000000000 : ℝ) (62425539349/125000000000 : ℝ) (124851078701/250000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4081/32768 : ℝ))) 5 (124851078701/250000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4081/32768 : ℝ))) 6 (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4081/32768 : ℝ))) 7 (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4081/32768 : ℝ)) hmem 8 (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4081/32768 : ℝ))) hcmem 8 (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4081/32768 : ℝ)) (198452271211/200000000000 : ℝ) (496130678029/500000000000 : ℝ) (499404314803/1000000000000 : ℝ) (499404314813/1000000000000 : ℝ) (98822560519/125000000000 : ℝ) (790580484171/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0159_exp_lower
  have heNumeric : (2054928089697/1000000000000 : ℝ)/4 ≤ Real.exp (-10656856106111/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054928089697/1000000000000 : ℝ)/4 ≤ Real.exp ((8161/65536 : ℝ)-(790580484171/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8161/65536 : ℝ) (4081/32768 : ℝ) (790580484171/1000000000000 : ℝ) (2054928089697/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0160; no trusted numerical premise.
theorem cover8_leaf0160_exp_radius : (998055681779127251/1000000000000000000 : ℝ) ≤ Real.exp ((-8163/524288 : ℝ)/8) ∧ Real.exp ((-8163/524288 : ℝ)/8) ≤ (249513920444781813/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8163/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0160_exp_lower : (920114904459556343/1000000000000000000 : ℝ) ≤ Real.exp ((-5328430117519/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328430117519/8000000000000 : ℝ)/8) ≤ (115014363057444543/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328430117519/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0160_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027463779703/500000000000 : ℝ) ≤ 4*Real.exp (4081/32768 : ℝ)*Real.exp (-mu (radius 8 (8163/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027463779703/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8163/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0160_exp_radius
  have hrNumeric : (984550894071/1000000000000 : ℝ) ≤ Real.exp (-8163/524288 : ℝ) ∧ Real.exp (-8163/524288 : ℝ) ≤ (123068861759/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984550894071/1000000000000 : ℝ) ≤ (radius 8 (8163/65536 : ℝ)) ∧ (radius 8 (8163/65536 : ℝ)) ≤ (123068861759/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8163/65536 : ℝ)) (984550894071/1000000000000 : ℝ) (123068861759/125000000000 : ℝ) (87549324643/500000000000 : ℝ) (175098649293/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8163/65536 : ℝ)) (984550894071/1000000000000 : ℝ) (123068861759/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8163/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984550894071/1000000000000 : ℝ) (123068861759/125000000000 : ℝ) (198455089407/200000000000 : ℝ) (248068861759/250000000000 : ℝ) (992245379969/1000000000000 : ℝ) (992245379971/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8163/65536 : ℝ)) 1 (198455089407/200000000000 : ℝ) (248068861759/250000000000 : ℝ) (992245379969/1000000000000 : ℝ) (992245379971/1000000000000 : ℝ) (496130206751/500000000000 : ℝ) (15504068961/15625000000 : ℝ) (248065103347/250000000000 : ℝ) (99226041339/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8163/65536 : ℝ)) 2 (496130206751/500000000000 : ℝ) (15504068961/15625000000 : ℝ) (248065103347/250000000000 : ℝ) (99226041339/100000000000 : ℝ) (198452082689/200000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8163/65536 : ℝ)) 3 (198452082689/200000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8163/65536 : ℝ)) 4 (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8163/65536 : ℝ)) 5 (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8163/65536 : ℝ)) 6 (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8163/65536 : ℝ)) 7 (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8163/65536 : ℝ))) (87549324643/500000000000 : ℝ) (175098649293/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8163/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87549324643/500000000000 : ℝ) (175098649293/1000000000000 : ℝ) (587549324643/1000000000000 : ℝ) (587549324647/1000000000000 : ℝ) (26152994069/62500000000 : ℝ) (418447905113/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8163/65536 : ℝ))) 1 (587549324643/1000000000000 : ℝ) (587549324647/1000000000000 : ℝ) (26152994069/62500000000 : ℝ) (418447905113/1000000000000 : ℝ) (502998614873/1000000000000 : ℝ) (3143741343/6250000000 : ℝ) (495841490843/1000000000000 : ℝ) (495841490851/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8163/65536 : ℝ))) 2 (502998614873/1000000000000 : ℝ) (3143741343/6250000000 : ℝ) (495841490843/1000000000000 : ℝ) (495841490851/1000000000000 : ℝ) (249710026429/500000000000 : ℝ) (249710026433/500000000000 : ℝ) (124851807929/250000000000 : ℝ) (124851807931/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8163/65536 : ℝ))) 3 (249710026429/500000000000 : ℝ) (249710026433/500000000000 : ℝ) (124851807929/250000000000 : ℝ) (124851807931/250000000000 : ℝ) (499413642287/1000000000000 : ℝ) (99882728459/200000000000 : ℝ) (99882728449/200000000000 : ℝ) (249706821127/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8163/65536 : ℝ))) 4 (499413642287/1000000000000 : ℝ) (99882728459/200000000000 : ℝ) (99882728449/200000000000 : ℝ) (249706821127/500000000000 : ℝ) (249706821133/500000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8163/65536 : ℝ))) 5 (249706821133/500000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8163/65536 : ℝ))) 6 (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8163/65536 : ℝ))) 7 (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8163/65536 : ℝ)) hmem 8 (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8163/65536 : ℝ))) hcmem 8 (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8163/65536 : ℝ)) (248065103361/250000000000 : ℝ) (992260413447/1000000000000 : ℝ) (99882728453/200000000000 : ℝ) (19976545691/40000000000 : ℝ) (790596000999/1000000000000 : ℝ) (395298000509/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0160_exp_lower
  have heNumeric : (1027463779703/500000000000 : ℝ)/4 ≤ Real.exp (-5328430117519/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027463779703/500000000000 : ℝ)/4 ≤ Real.exp ((4081/32768 : ℝ)-(395298000509/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4081/32768 : ℝ) (8163/65536 : ℝ) (395298000509/500000000000 : ℝ) (1027463779703/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0161; no trusted numerical premise.
theorem cover8_leaf0161_exp_radius : (998055443824138103/1000000000000000000 : ℝ) ≤ Real.exp ((-2041/131072 : ℝ)/8) ∧ Real.exp ((-2041/131072 : ℝ)/8) ≤ (124756930478017263/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2041/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0161_exp_lower : (460057437464123059/500000000000000000 : ℝ) ≤ Real.exp ((-10656864343229/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656864343229/16000000000000 : ℝ)/8) ≤ (920114874928246119/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656864343229/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0161_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054927031779/1000000000000 : ℝ) ≤ 4*Real.exp (8163/65536 : ℝ)*Real.exp (-mu (radius 8 (2041/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054927031779/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2041/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0161_exp_radius
  have hrNumeric : (984549016191/1000000000000 : ℝ) ≤ Real.exp (-2041/131072 : ℝ) ∧ Real.exp (-2041/131072 : ℝ) ≤ (7691789189/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984549016191/1000000000000 : ℝ) ≤ (radius 8 (2041/16384 : ℝ)) ∧ (radius 8 (2041/16384 : ℝ)) ≤ (7691789189/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2041/16384 : ℝ)) (984549016191/1000000000000 : ℝ) (7691789189/7812500000 : ℝ) (5472162749/31250000000 : ℝ) (7004368319/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2041/16384 : ℝ)) (984549016191/1000000000000 : ℝ) (7691789189/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2041/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984549016191/1000000000000 : ℝ) (7691789189/7812500000 : ℝ) (198454901619/200000000000 : ℝ) (15504289189/15625000000 : ℝ) (992244433691/1000000000000 : ℝ) (248061108423/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2041/16384 : ℝ)) 1 (198454901619/200000000000 : ℝ) (15504289189/15625000000 : ℝ) (992244433691/1000000000000 : ℝ) (248061108423/250000000000 : ℝ) (992259470893/1000000000000 : ℝ) (496129735447/500000000000 : ℝ) (992259470779/1000000000000 : ℝ) (992259470781/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2041/16384 : ℝ)) 2 (992259470893/1000000000000 : ℝ) (496129735447/500000000000 : ℝ) (992259470779/1000000000000 : ℝ) (992259470781/1000000000000 : ℝ) (248064867709/250000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2041/16384 : ℝ)) 3 (248064867709/250000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2041/16384 : ℝ)) 4 (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2041/16384 : ℝ)) 5 (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2041/16384 : ℝ)) 6 (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2041/16384 : ℝ)) 7 (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2041/16384 : ℝ))) (5472162749/31250000000 : ℝ) (7004368319/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2041/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5472162749/31250000000 : ℝ) (7004368319/40000000000 : ℝ) (36722162749/62500000000 : ℝ) (146888650997/250000000000 : ℝ) (418460521397/1000000000000 : ℝ) (209230260703/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2041/16384 : ℝ))) 1 (36722162749/62500000000 : ℝ) (146888650997/250000000000 : ℝ) (418460521397/1000000000000 : ℝ) (209230260703/500000000000 : ℝ) (50300756269/100000000000 : ℝ) (503007562697/1000000000000 : ℝ) (99170238667/200000000000 : ℝ) (495851193343/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2041/16384 : ℝ))) 2 (50300756269/100000000000 : ℝ) (503007562697/1000000000000 : ℝ) (99170238667/200000000000 : ℝ) (495851193343/1000000000000 : ℝ) (124857344503/250000000000 : ℝ) (24971468901/50000000000 : ℝ) (499416559813/1000000000000 : ℝ) (249708279911/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2041/16384 : ℝ))) 3 (124857344503/250000000000 : ℝ) (24971468901/50000000000 : ℝ) (499416559813/1000000000000 : ℝ) (249708279911/500000000000 : ℝ) (31213935557/62500000000 : ℝ) (499422968921/1000000000000 : ℝ) (499422968871/1000000000000 : ℝ) (6242787111/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2041/16384 : ℝ))) 4 (31213935557/62500000000 : ℝ) (499422968921/1000000000000 : ℝ) (499422968871/1000000000000 : ℝ) (6242787111/12500000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2041/16384 : ℝ))) 5 (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2041/16384 : ℝ))) 6 (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2041/16384 : ℝ))) 7 (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2041/16384 : ℝ)) hmem 8 (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2041/16384 : ℝ))) hcmem 8 (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2041/16384 : ℝ)) (198451894167/200000000000 : ℝ) (496129735419/500000000000 : ℝ) (499422968891/1000000000000 : ℝ) (499422968901/1000000000000 : ℝ) (15812230331/20000000000 : ℝ) (790611516569/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0161_exp_lower
  have heNumeric : (2054927031779/1000000000000 : ℝ)/4 ≤ Real.exp (-10656864343229/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054927031779/1000000000000 : ℝ)/4 ≤ Real.exp ((8163/65536 : ℝ)-(790611516569/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8163/65536 : ℝ) (2041/16384 : ℝ) (790611516569/1000000000000 : ℝ) (2054927031779/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0162; no trusted numerical premise.
theorem cover8_leaf0162_exp_radius : (124756900733650711/125000000000000000 : ℝ) ≤ Real.exp ((-8165/524288 : ℝ)/8) ∧ Real.exp ((-8165/524288 : ℝ)/8) ≤ (998055205869205689/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8165/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0162_exp_lower : (920114845545765417/1000000000000000000 : ℝ) ≤ Real.exp ((-2664217107679/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664217107679/4000000000000 : ℝ)/8) ≤ (460057422772882709/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664217107679/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0162_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054926506811/1000000000000 : ℝ) ≤ 4*Real.exp (2041/16384 : ℝ)*Real.exp (-mu (radius 8 (8165/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054926506811/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8165/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0162_exp_radius
  have hrNumeric : (196909427663/200000000000 : ℝ) ≤ Real.exp (-8165/524288 : ℝ) ∧ Real.exp (-8165/524288 : ℝ) ≤ (246136784579/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196909427663/200000000000 : ℝ) ≤ (radius 8 (8165/65536 : ℝ)) ∧ (radius 8 (8165/65536 : ℝ)) ≤ (246136784579/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8165/65536 : ℝ)) (196909427663/200000000000 : ℝ) (246136784579/250000000000 : ℝ) (175119765971/1000000000000 : ℝ) (175119765977/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8165/65536 : ℝ)) (196909427663/200000000000 : ℝ) (246136784579/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8165/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196909427663/200000000000 : ℝ) (246136784579/250000000000 : ℝ) (992273569157/1000000000000 : ℝ) (496136784579/500000000000 : ℝ) (992243487413/1000000000000 : ℝ) (198448697483/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8165/65536 : ℝ)) 1 (992273569157/1000000000000 : ℝ) (496136784579/500000000000 : ℝ) (992243487413/1000000000000 : ℝ) (198448697483/200000000000 : ℝ) (198451705657/200000000000 : ℝ) (992258528287/1000000000000 : ℝ) (992258528171/1000000000000 : ℝ) (992258528173/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8165/65536 : ℝ)) 2 (198451705657/200000000000 : ℝ) (992258528287/1000000000000 : ℝ) (992258528171/1000000000000 : ℝ) (992258528173/1000000000000 : ℝ) (248064632057/250000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8165/65536 : ℝ)) 3 (248064632057/250000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8165/65536 : ℝ)) 4 (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8165/65536 : ℝ)) 5 (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8165/65536 : ℝ)) 6 (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8165/65536 : ℝ)) 7 (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8165/65536 : ℝ))) (175119765971/1000000000000 : ℝ) (175119765977/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8165/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175119765971/1000000000000 : ℝ) (175119765977/1000000000000 : ℝ) (117511976597/200000000000 : ℝ) (587559882989/1000000000000 : ℝ) (209236568249/500000000000 : ℝ) (209236568253/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8165/65536 : ℝ))) 1 (117511976597/200000000000 : ℝ) (587559882989/1000000000000 : ℝ) (209236568249/500000000000 : ℝ) (209236568253/500000000000 : ℝ) (503016509741/1000000000000 : ℝ) (125754127437/250000000000 : ℝ) (247930447461/500000000000 : ℝ) (495860894929/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8165/65536 : ℝ))) 2 (503016509741/1000000000000 : ℝ) (125754127437/250000000000 : ℝ) (247930447461/500000000000 : ℝ) (495860894929/1000000000000 : ℝ) (499438702331/1000000000000 : ℝ) (499438702339/1000000000000 : ℝ) (19977035483/40000000000 : ℝ) (499425887083/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8165/65536 : ℝ))) 3 (499438702331/1000000000000 : ℝ) (499438702339/1000000000000 : ℝ) (19977035483/40000000000 : ℝ) (499425887083/1000000000000 : ℝ) (499432294703/1000000000000 : ℝ) (499432294711/1000000000000 : ℝ) (499432294661/1000000000000 : ℝ) (49943229467/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8165/65536 : ℝ))) 4 (499432294703/1000000000000 : ℝ) (499432294711/1000000000000 : ℝ) (499432294661/1000000000000 : ℝ) (49943229467/100000000000 : ℝ) (249716147341/500000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8165/65536 : ℝ))) 5 (249716147341/500000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8165/65536 : ℝ))) 6 (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8165/65536 : ℝ))) 7 (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8165/65536 : ℝ)) hmem 8 (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8165/65536 : ℝ))) hcmem 8 (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8165/65536 : ℝ)) (992258528227/1000000000000 : ℝ) (99225852823/100000000000 : ℝ) (499432294681/1000000000000 : ℝ) (499432294691/1000000000000 : ℝ) (790627030807/1000000000000 : ℝ) (395313515413/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0162_exp_lower
  have heNumeric : (2054926506811/1000000000000 : ℝ)/4 ≤ Real.exp (-2664217107679/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054926506811/1000000000000 : ℝ)/4 ≤ Real.exp ((2041/16384 : ℝ)-(395313515413/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2041/16384 : ℝ) (8165/65536 : ℝ) (395313515413/500000000000 : ℝ) (2054926506811/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0163; no trusted numerical premise.
theorem cover8_leaf0163_exp_radius : (499027483957165003/500000000000000000 : ℝ) ≤ Real.exp ((-4083/262144 : ℝ)/8) ∧ Real.exp ((-4083/262144 : ℝ)/8) ≤ (998054967914330007/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4083/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0163_exp_lower : (7360918530490473/8000000000000000 : ℝ) ≤ Real.exp ((-10656872497611/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656872497611/16000000000000 : ℝ)/8) ≤ (460057408155654563/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656872497611/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0163_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256865748061/125000000000 : ℝ) ≤ 4*Real.exp (8165/65536 : ℝ)*Real.exp (-mu (radius 8 (4083/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (256865748061/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4083/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0163_exp_radius
  have hrNumeric : (492272630221/500000000000 : ℝ) ≤ Real.exp (-4083/262144 : ℝ) ∧ Real.exp (-4083/262144 : ℝ) ≤ (984545260443/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492272630221/500000000000 : ℝ) ≤ (radius 8 (4083/32768 : ℝ)) ∧ (radius 8 (4083/32768 : ℝ)) ≤ (984545260443/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4083/32768 : ℝ)) (492272630221/500000000000 : ℝ) (984545260443/1000000000000 : ℝ) (1751303233/10000000000 : ℝ) (87565161653/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4083/32768 : ℝ)) (492272630221/500000000000 : ℝ) (984545260443/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4083/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492272630221/500000000000 : ℝ) (984545260443/1000000000000 : ℝ) (992272630221/1000000000000 : ℝ) (496136315111/500000000000 : ℝ) (62015158821/62500000000 : ℝ) (496121270569/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4083/32768 : ℝ)) 1 (992272630221/1000000000000 : ℝ) (496136315111/500000000000 : ℝ) (62015158821/62500000000 : ℝ) (496121270569/500000000000 : ℝ) (496128792839/500000000000 : ℝ) (12403219821/12500000000 : ℝ) (248064396391/250000000000 : ℝ) (496128792783/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4083/32768 : ℝ)) 2 (496128792839/500000000000 : ℝ) (12403219821/12500000000 : ℝ) (248064396391/250000000000 : ℝ) (496128792783/500000000000 : ℝ) (992257585621/1000000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4083/32768 : ℝ)) 3 (992257585621/1000000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4083/32768 : ℝ)) 4 (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4083/32768 : ℝ)) 5 (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4083/32768 : ℝ)) 6 (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4083/32768 : ℝ)) 7 (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4083/32768 : ℝ))) (1751303233/10000000000 : ℝ) (87565161653/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4083/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1751303233/10000000000 : ℝ) (87565161653/500000000000 : ℝ) (11751303233/20000000000 : ℝ) (587565161653/1000000000000 : ℝ) (209242875207/500000000000 : ℝ) (209242875211/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4083/32768 : ℝ))) 1 (11751303233/20000000000 : ℝ) (587565161653/1000000000000 : ℝ) (209242875207/500000000000 : ℝ) (209242875211/500000000000 : ℝ) (15719545501/31250000000 : ℝ) (251512728019/500000000000 : ℝ) (495870595609/1000000000000 : ℝ) (15495956113/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4083/32768 : ℝ))) 2 (15719545501/31250000000 : ℝ) (251512728019/500000000000 : ℝ) (495870595609/1000000000000 : ℝ) (15495956113/31250000000 : ℝ) (24972401291/50000000000 : ℝ) (499448025827/1000000000000 : ℝ) (99887042701/200000000000 : ℝ) (62429401689/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4083/32768 : ℝ))) 3 (24972401291/50000000000 : ℝ) (499448025827/1000000000000 : ℝ) (99887042701/200000000000 : ℝ) (62429401689/125000000000 : ℝ) (249720809831/500000000000 : ℝ) (49944161967/100000000000 : ℝ) (499441619621/1000000000000 : ℝ) (499441619629/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4083/32768 : ℝ))) 4 (249720809831/500000000000 : ℝ) (49944161967/100000000000 : ℝ) (499441619621/1000000000000 : ℝ) (499441619629/1000000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4083/32768 : ℝ))) 5 (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4083/32768 : ℝ))) 6 (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4083/32768 : ℝ))) 7 (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4083/32768 : ℝ)) hmem 8 (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4083/32768 : ℝ))) hcmem 8 (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4083/32768 : ℝ)) (49612879281/50000000000 : ℝ) (992257585623/1000000000000 : ℝ) (499441619641/1000000000000 : ℝ) (9988832393/20000000000 : ℝ) (395321271889/500000000000 : ℝ) (197660635949/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0163_exp_lower
  have heNumeric : (256865748061/125000000000 : ℝ)/4 ≤ Real.exp (-10656872497611/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256865748061/125000000000 : ℝ)/4 ≤ Real.exp ((8165/65536 : ℝ)-(197660635949/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8165/65536 : ℝ) (4083/32768 : ℝ) (197660635949/250000000000 : ℝ) (256865748061/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0164; no trusted numerical premise.
theorem cover8_leaf0164_exp_radius : (998054729959511057/1000000000000000000 : ℝ) ≤ Real.exp ((-8167/524288 : ℝ)/8) ∧ Real.exp ((-8167/524288 : ℝ)/8) ≤ (499027364979755529/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8167/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0164_exp_lower : (920114787224877229/1000000000000000000 : ℝ) ≤ Real.exp ((-5328438271957/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328438271957/8000000000000 : ℝ)/8) ≤ (92011478722487723/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328438271957/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0164_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205492546481/100000000000 : ℝ) ≤ 4*Real.exp (4083/32768 : ℝ)*Real.exp (-mu (radius 8 (8167/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205492546481/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8167/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0164_exp_radius
  have hrNumeric : (246135845643/250000000000 : ℝ) ≤ Real.exp (-8167/524288 : ℝ) ∧ Real.exp (-8167/524288 : ℝ) ≤ (984543382573/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246135845643/250000000000 : ℝ) ≤ (radius 8 (8167/65536 : ℝ)) ∧ (radius 8 (8167/65536 : ℝ)) ≤ (984543382573/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8167/65536 : ℝ)) (246135845643/250000000000 : ℝ) (984543382573/1000000000000 : ℝ) (35028175991/200000000000 : ℝ) (87570439981/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8167/65536 : ℝ)) (246135845643/250000000000 : ℝ) (984543382573/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8167/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246135845643/250000000000 : ℝ) (984543382573/1000000000000 : ℝ) (496135845643/500000000000 : ℝ) (992271691287/1000000000000 : ℝ) (49612079743/50000000000 : ℝ) (496120797431/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8167/65536 : ℝ)) 1 (496135845643/500000000000 : ℝ) (992271691287/1000000000000 : ℝ) (49612079743/50000000000 : ℝ) (496120797431/500000000000 : ℝ) (992256643073/1000000000000 : ℝ) (39690265723/40000000000 : ℝ) (496128321479/500000000000 : ℝ) (992256642961/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8167/65536 : ℝ)) 2 (992256643073/1000000000000 : ℝ) (39690265723/40000000000 : ℝ) (496128321479/500000000000 : ℝ) (992256642961/1000000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8167/65536 : ℝ)) 3 (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8167/65536 : ℝ)) 4 (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8167/65536 : ℝ)) 5 (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8167/65536 : ℝ)) 6 (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8167/65536 : ℝ)) 7 (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8167/65536 : ℝ))) (35028175991/200000000000 : ℝ) (87570439981/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8167/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35028175991/200000000000 : ℝ) (87570439981/500000000000 : ℝ) (587570439977/1000000000000 : ℝ) (587570439981/1000000000000 : ℝ) (52312295393/125000000000 : ℝ) (209249181577/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8167/65536 : ℝ))) 1 (587570439977/1000000000000 : ℝ) (587570439981/1000000000000 : ℝ) (52312295393/125000000000 : ℝ) (209249181577/500000000000 : ℝ) (12575860039/25000000000 : ℝ) (15719825049/31250000000 : ℝ) (123970073849/250000000000 : ℝ) (123970073851/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8167/65536 : ℝ))) 2 (12575860039/25000000000 : ℝ) (15719825049/31250000000 : ℝ) (123970073849/250000000000 : ℝ) (123970073851/250000000000 : ℝ) (249728674239/500000000000 : ℝ) (249728674243/500000000000 : ℝ) (499444539103/1000000000000 : ℝ) (62430567389/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8167/65536 : ℝ))) 3 (249728674239/500000000000 : ℝ) (249728674243/500000000000 : ℝ) (499444539103/1000000000000 : ℝ) (62430567389/125000000000 : ℝ) (49945094379/100000000000 : ℝ) (499450943799/1000000000000 : ℝ) (499450943749/1000000000000 : ℝ) (249725471879/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8167/65536 : ℝ))) 4 (49945094379/100000000000 : ℝ) (499450943799/1000000000000 : ℝ) (499450943749/1000000000000 : ℝ) (249725471879/500000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8167/65536 : ℝ))) 5 (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8167/65536 : ℝ))) 6 (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8167/65536 : ℝ))) 7 (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8167/65536 : ℝ)) hmem 8 (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8167/65536 : ℝ))) hcmem 8 (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8167/65536 : ℝ)) (198451328603/200000000000 : ℝ) (496128321509/500000000000 : ℝ) (499450943769/1000000000000 : ℝ) (499450943779/1000000000000 : ℝ) (39532902773/50000000000 : ℝ) (790658055479/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0164_exp_lower
  have heNumeric : (205492546481/100000000000 : ℝ)/4 ≤ Real.exp (-5328438271957/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205492546481/100000000000 : ℝ)/4 ≤ Real.exp ((4083/32768 : ℝ)-(790658055479/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4083/32768 : ℝ) (8167/65536 : ℝ) (790658055479/1000000000000 : ℝ) (205492546481/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0165; no trusted numerical premise.
theorem cover8_leaf0165_exp_radius : (998054492004748841/1000000000000000000 : ℝ) ≤ Real.exp ((-1021/65536 : ℝ)/8) ∧ Real.exp ((-1021/65536 : ℝ)/8) ≤ (499027246002374421/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1021/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0165_exp_lower : (9201147582879649/10000000000000000 : ℝ) ≤ Real.exp ((-10656880569417/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656880569417/16000000000000 : ℝ)/8) ≤ (920114758287964901/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656880569417/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0165_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054924947803/1000000000000 : ℝ) ≤ 4*Real.exp (8167/65536 : ℝ)*Real.exp (-mu (radius 8 (1021/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054924947803/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1021/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0165_exp_radius
  have hrNumeric : (984541504707/1000000000000 : ℝ) ≤ Real.exp (-1021/65536 : ℝ) ∧ Real.exp (-1021/65536 : ℝ) ≤ (246135376177/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984541504707/1000000000000 : ℝ) ≤ (radius 8 (1021/8192 : ℝ)) ∧ (radius 8 (1021/8192 : ℝ)) ≤ (246135376177/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1021/8192 : ℝ)) (984541504707/1000000000000 : ℝ) (246135376177/250000000000 : ℝ) (175151435927/1000000000000 : ℝ) (175151435933/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1021/8192 : ℝ)) (984541504707/1000000000000 : ℝ) (246135376177/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1021/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984541504707/1000000000000 : ℝ) (246135376177/250000000000 : ℝ) (992270752353/1000000000000 : ℝ) (496135376177/500000000000 : ℝ) (496120324293/500000000000 : ℝ) (992240648587/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1021/8192 : ℝ)) 1 (992270752353/1000000000000 : ℝ) (496135376177/500000000000 : ℝ) (496120324293/500000000000 : ℝ) (992240648587/1000000000000 : ℝ) (992255700469/1000000000000 : ℝ) (992255700471/1000000000000 : ℝ) (198451140071/200000000000 : ℝ) (992255700357/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1021/8192 : ℝ)) 2 (992255700469/1000000000000 : ℝ) (992255700471/1000000000000 : ℝ) (198451140071/200000000000 : ℝ) (992255700357/1000000000000 : ℝ) (248063925103/250000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1021/8192 : ℝ)) 3 (248063925103/250000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1021/8192 : ℝ)) 4 (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1021/8192 : ℝ)) 5 (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1021/8192 : ℝ)) 6 (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1021/8192 : ℝ)) 7 (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1021/8192 : ℝ))) (175151435927/1000000000000 : ℝ) (175151435933/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1021/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175151435927/1000000000000 : ℝ) (175151435933/1000000000000 : ℝ) (587575717963/1000000000000 : ℝ) (587575717967/1000000000000 : ℝ) (418510974679/1000000000000 : ℝ) (418510974687/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1021/8192 : ℝ))) 1 (587575717963/1000000000000 : ℝ) (587575717967/1000000000000 : ℝ) (418510974679/1000000000000 : ℝ) (418510974687/1000000000000 : ℝ) (503043346321/1000000000000 : ℝ) (503043346327/1000000000000 : ℝ) (19835599771/40000000000 : ℝ) (247944997141/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1021/8192 : ℝ))) 2 (503043346321/1000000000000 : ℝ) (503043346327/1000000000000 : ℝ) (19835599771/40000000000 : ℝ) (247944997141/500000000000 : ℝ) (249733335149/500000000000 : ℝ) (99893334061/200000000000 : ℝ) (249726931931/500000000000 : ℝ) (49945386387/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1021/8192 : ℝ))) 3 (249733335149/500000000000 : ℝ) (99893334061/200000000000 : ℝ) (249726931931/500000000000 : ℝ) (49945386387/100000000000 : ℝ) (12486506677/25000000000 : ℝ) (31216266693/62500000000 : ℝ) (249730133519/500000000000 : ℝ) (499460267047/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1021/8192 : ℝ))) 4 (12486506677/25000000000 : ℝ) (31216266693/62500000000 : ℝ) (249730133519/500000000000 : ℝ) (499460267047/1000000000000 : ℝ) (499460267059/1000000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1021/8192 : ℝ))) 5 (499460267059/1000000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1021/8192 : ℝ))) 6 (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1021/8192 : ℝ))) 7 (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1021/8192 : ℝ)) hmem 8 (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1021/8192 : ℝ))) hcmem 8 (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1021/8192 : ℝ)) (992255700411/1000000000000 : ℝ) (496127850207/500000000000 : ℝ) (249730133529/500000000000 : ℝ) (124865066767/250000000000 : ℝ) (790673565843/1000000000000 : ℝ) (395336782931/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0165_exp_lower
  have heNumeric : (2054924947803/1000000000000 : ℝ)/4 ≤ Real.exp (-10656880569417/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054924947803/1000000000000 : ℝ)/4 ≤ Real.exp ((8167/65536 : ℝ)-(395336782931/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8167/65536 : ℝ) (1021/8192 : ℝ) (395336782931/500000000000 : ℝ) (2054924947803/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0166; no trusted numerical premise.
theorem cover8_leaf0166_exp_radius : (499027127025021679/500000000000000000 : ℝ) ≤ Real.exp ((-8169/524288 : ℝ)/8) ∧ Real.exp ((-8169/524288 : ℝ)/8) ≤ (998054254050043359/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8169/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0166_exp_lower : (920114729499191953/1000000000000000000 : ℝ) ≤ Real.exp ((-1332110571789/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332110571789/2000000000000 : ℝ)/8) ≤ (460057364749595977/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332110571789/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0166_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513731108361/250000000000 : ℝ) ≤ 4*Real.exp (1021/8192 : ℝ)*Real.exp (-mu (radius 8 (8169/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513731108361/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8169/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0166_exp_radius
  have hrNumeric : (196907925369/200000000000 : ℝ) ≤ Real.exp (-8169/524288 : ℝ) ∧ Real.exp (-8169/524288 : ℝ) ≤ (492269813423/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196907925369/200000000000 : ℝ) ≤ (radius 8 (8169/65536 : ℝ)) ∧ (radius 8 (8169/65536 : ℝ)) ≤ (492269813423/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8169/65536 : ℝ)) (196907925369/200000000000 : ℝ) (492269813423/500000000000 : ℝ) (7006479649/40000000000 : ℝ) (175161991231/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8169/65536 : ℝ)) (196907925369/200000000000 : ℝ) (492269813423/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8169/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196907925369/200000000000 : ℝ) (492269813423/500000000000 : ℝ) (496134906711/500000000000 : ℝ) (992269813423/1000000000000 : ℝ) (124029962789/125000000000 : ℝ) (992239702313/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8169/65536 : ℝ)) 1 (496134906711/500000000000 : ℝ) (992269813423/1000000000000 : ℝ) (124029962789/125000000000 : ℝ) (992239702313/1000000000000 : ℝ) (992254757867/1000000000000 : ℝ) (248063689467/250000000000 : ℝ) (124031844719/125000000000 : ℝ) (496127378877/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8169/65536 : ℝ)) 2 (992254757867/1000000000000 : ℝ) (248063689467/250000000000 : ℝ) (124031844719/125000000000 : ℝ) (496127378877/500000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8169/65536 : ℝ)) 3 (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8169/65536 : ℝ)) 4 (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8169/65536 : ℝ)) 5 (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8169/65536 : ℝ)) 6 (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8169/65536 : ℝ)) 7 (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8169/65536 : ℝ))) (7006479649/40000000000 : ℝ) (175161991231/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8169/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7006479649/40000000000 : ℝ) (175161991231/1000000000000 : ℝ) (146895248903/250000000000 : ℝ) (18361906113/31250000000 : ℝ) (104630896257/250000000000 : ℝ) (104630896259/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8169/65536 : ℝ))) 1 (146895248903/250000000000 : ℝ) (18361906113/31250000000 : ℝ) (104630896257/250000000000 : ℝ) (104630896259/250000000000 : ℝ) (6288153629/12500000000 : ℝ) (251526145163/500000000000 : ℝ) (247949846127/500000000000 : ℝ) (495899692261/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8169/65536 : ℝ))) 2 (6288153629/12500000000 : ℝ) (251526145163/500000000000 : ℝ) (247949846127/500000000000 : ℝ) (495899692261/1000000000000 : ℝ) (499475991287/1000000000000 : ℝ) (249737995647/500000000000 : ℝ) (49946318779/100000000000 : ℝ) (499463187797/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8169/65536 : ℝ))) 3 (499475991287/1000000000000 : ℝ) (249737995647/500000000000 : ℝ) (49946318779/100000000000 : ℝ) (499463187797/1000000000000 : ℝ) (249734794769/500000000000 : ℝ) (249734794773/500000000000 : ℝ) (499469589497/1000000000000 : ℝ) (99893917901/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8169/65536 : ℝ))) 4 (249734794769/500000000000 : ℝ) (249734794773/500000000000 : ℝ) (499469589497/1000000000000 : ℝ) (99893917901/200000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8169/65536 : ℝ))) 5 (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8169/65536 : ℝ))) 6 (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8169/65536 : ℝ))) 7 (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8169/65536 : ℝ)) hmem 8 (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8169/65536 : ℝ))) hcmem 8 (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8169/65536 : ℝ)) (992254757809/1000000000000 : ℝ) (992254757811/1000000000000 : ℝ) (499469589517/1000000000000 : ℝ) (249734794763/500000000000 : ℝ) (39534453747/50000000000 : ℝ) (790689074957/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0166_exp_lower
  have heNumeric : (513731108361/250000000000 : ℝ)/4 ≤ Real.exp (-1332110571789/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513731108361/250000000000 : ℝ)/4 ≤ Real.exp ((1021/8192 : ℝ)-(790689074957/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1021/8192 : ℝ) (8169/65536 : ℝ) (790689074957/1000000000000 : ℝ) (513731108361/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0167; no trusted numerical premise.
theorem cover8_leaf0167_exp_radius : (62378376005962163/62500000000000000 : ℝ) ≤ Real.exp ((-4085/262144 : ℝ)/8) ∧ Real.exp ((-4085/262144 : ℝ)/8) ≤ (998054016095394609/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4085/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0167_exp_lower : (92011470085821333/100000000000000000 : ℝ) ≤ Real.exp ((-10656888558647/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656888558647/16000000000000 : ℝ)/8) ≤ (920114700858213331/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656888558647/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0167_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513730980431/250000000000 : ℝ) ≤ 4*Real.exp (8169/65536 : ℝ)*Real.exp (-mu (radius 8 (4085/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513730980431/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4085/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0167_exp_radius
  have hrNumeric : (492268874493/500000000000 : ℝ) ≤ Real.exp (-4085/262144 : ℝ) ∧ Real.exp (-4085/262144 : ℝ) ≤ (984537748987/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492268874493/500000000000 : ℝ) ≤ (radius 8 (4085/32768 : ℝ)) ∧ (radius 8 (4085/32768 : ℝ)) ≤ (984537748987/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4085/32768 : ℝ)) (492268874493/500000000000 : ℝ) (984537748987/1000000000000 : ℝ) (3503450917/20000000000 : ℝ) (2737071029/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4085/32768 : ℝ)) (492268874493/500000000000 : ℝ) (984537748987/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4085/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492268874493/500000000000 : ℝ) (984537748987/1000000000000 : ℝ) (992268874493/1000000000000 : ℝ) (496134437247/500000000000 : ℝ) (992238756039/1000000000000 : ℝ) (24805968901/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4085/32768 : ℝ)) 1 (992268874493/1000000000000 : ℝ) (496134437247/500000000000 : ℝ) (992238756039/1000000000000 : ℝ) (24805968901/25000000000 : ℝ) (496126907633/500000000000 : ℝ) (992253815267/1000000000000 : ℝ) (992253815151/1000000000000 : ℝ) (992253815153/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4085/32768 : ℝ)) 2 (496126907633/500000000000 : ℝ) (992253815267/1000000000000 : ℝ) (992253815151/1000000000000 : ℝ) (992253815153/1000000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4085/32768 : ℝ)) 3 (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4085/32768 : ℝ)) 4 (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4085/32768 : ℝ)) 5 (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4085/32768 : ℝ)) 6 (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4085/32768 : ℝ)) 7 (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4085/32768 : ℝ))) (3503450917/20000000000 : ℝ) (2737071029/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4085/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3503450917/20000000000 : ℝ) (2737071029/15625000000 : ℝ) (23503450917/40000000000 : ℝ) (18362071029/31250000000 : ℝ) (418536194193/1000000000000 : ℝ) (418536194201/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4085/32768 : ℝ))) 1 (23503450917/40000000000 : ℝ) (18362071029/31250000000 : ℝ) (418536194193/1000000000000 : ℝ) (418536194201/1000000000000 : ℝ) (503061233559/1000000000000 : ℝ) (100612246713/200000000000 : ℝ) (247954694667/500000000000 : ℝ) (495909389341/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4085/32768 : ℝ))) 2 (503061233559/1000000000000 : ℝ) (100612246713/200000000000 : ℝ) (247954694667/500000000000 : ℝ) (495909389341/1000000000000 : ℝ) (249742655723/500000000000 : ℝ) (499485311453/1000000000000 : ℝ) (499472510887/1000000000000 : ℝ) (249736255447/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4085/32768 : ℝ))) 3 (249742655723/500000000000 : ℝ) (499485311453/1000000000000 : ℝ) (499472510887/1000000000000 : ℝ) (249736255447/500000000000 : ℝ) (249739455583/500000000000 : ℝ) (249739455587/500000000000 : ℝ) (3995831289/8000000000 : ℝ) (499478911133/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4085/32768 : ℝ))) 4 (249739455583/500000000000 : ℝ) (249739455587/500000000000 : ℝ) (3995831289/8000000000 : ℝ) (499478911133/1000000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4085/32768 : ℝ))) 5 (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4085/32768 : ℝ))) 6 (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4085/32768 : ℝ))) 7 (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4085/32768 : ℝ)) hmem 8 (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4085/32768 : ℝ))) hcmem 8 (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4085/32768 : ℝ)) (124031726901/125000000000 : ℝ) (99225381521/100000000000 : ℝ) (99895782229/200000000000 : ℝ) (249739455577/500000000000 : ℝ) (3162818331/4000000000 : ℝ) (790704582767/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0167_exp_lower
  have heNumeric : (513730980431/250000000000 : ℝ)/4 ≤ Real.exp (-10656888558647/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513730980431/250000000000 : ℝ)/4 ≤ Real.exp ((8169/65536 : ℝ)-(790704582767/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8169/65536 : ℝ) (4085/32768 : ℝ) (790704582767/1000000000000 : ℝ) (513730980431/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0168; no trusted numerical premise.
theorem cover8_leaf0168_exp_radius : (99805377814080259/100000000000000000 : ℝ) ≤ Real.exp ((-8171/524288 : ℝ)/8) ∧ Real.exp ((-8171/524288 : ℝ)/8) ≤ (998053778140802591/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8171/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0168_exp_lower : (14376791755714361/15625000000000000 : ℝ) ≤ Real.exp ((-5328446261163/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328446261163/8000000000000 : ℝ)/8) ≤ (184022934473143821/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328446261163/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0168_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027461706329/500000000000 : ℝ) ≤ 4*Real.exp (4085/32768 : ℝ)*Real.exp (-mu (radius 8 (8171/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027461706329/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8171/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0168_exp_radius
  have hrNumeric : (984535871131/1000000000000 : ℝ) ≤ Real.exp (-8171/524288 : ℝ) ∧ Real.exp (-8171/524288 : ℝ) ≤ (246133967783/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984535871131/1000000000000 : ℝ) ≤ (radius 8 (8171/65536 : ℝ)) ∧ (radius 8 (8171/65536 : ℝ)) ≤ (246133967783/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8171/65536 : ℝ)) (984535871131/1000000000000 : ℝ) (246133967783/250000000000 : ℝ) (43795774949/250000000000 : ℝ) (175183099803/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8171/65536 : ℝ)) (984535871131/1000000000000 : ℝ) (246133967783/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8171/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984535871131/1000000000000 : ℝ) (246133967783/250000000000 : ℝ) (198453587113/200000000000 : ℝ) (496133967783/500000000000 : ℝ) (496118904883/500000000000 : ℝ) (124029726221/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8171/65536 : ℝ)) 1 (198453587113/200000000000 : ℝ) (496133967783/500000000000 : ℝ) (496118904883/500000000000 : ℝ) (124029726221/125000000000 : ℝ) (198450574533/200000000000 : ℝ) (992252872667/1000000000000 : ℝ) (992252872551/1000000000000 : ℝ) (992252872553/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8171/65536 : ℝ)) 2 (198450574533/200000000000 : ℝ) (992252872667/1000000000000 : ℝ) (992252872551/1000000000000 : ℝ) (992252872553/1000000000000 : ℝ) (31007902269/31250000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8171/65536 : ℝ)) 3 (31007902269/31250000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8171/65536 : ℝ)) 4 (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8171/65536 : ℝ)) 5 (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8171/65536 : ℝ)) 6 (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8171/65536 : ℝ)) 7 (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8171/65536 : ℝ))) (43795774949/250000000000 : ℝ) (175183099803/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8171/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43795774949/250000000000 : ℝ) (175183099803/1000000000000 : ℝ) (293795774949/500000000000 : ℝ) (293795774951/500000000000 : ℝ) (418548802167/1000000000000 : ℝ) (418548802177/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8171/65536 : ℝ))) 1 (293795774949/500000000000 : ℝ) (293795774951/500000000000 : ℝ) (418548802167/1000000000000 : ℝ) (418548802177/1000000000000 : ℝ) (15720943001/31250000000 : ℝ) (12576754401/25000000000 : ℝ) (49591908551/100000000000 : ℝ) (247959542759/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8171/65536 : ℝ))) 2 (15720943001/31250000000 : ℝ) (12576754401/25000000000 : ℝ) (49591908551/100000000000 : ℝ) (247959542759/500000000000 : ℝ) (499494630771/1000000000000 : ℝ) (499494630779/1000000000000 : ℝ) (124870458287/250000000000 : ℝ) (499481833157/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8171/65536 : ℝ))) 3 (499494630771/1000000000000 : ℝ) (499494630779/1000000000000 : ℝ) (124870458287/250000000000 : ℝ) (499481833157/1000000000000 : ℝ) (499488231959/1000000000000 : ℝ) (15609007249/31250000000 : ℝ) (249744115959/500000000000 : ℝ) (62436028991/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8171/65536 : ℝ))) 4 (499488231959/1000000000000 : ℝ) (15609007249/31250000000 : ℝ) (249744115959/500000000000 : ℝ) (62436028991/125000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8171/65536 : ℝ))) 5 (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8171/65536 : ℝ))) 6 (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8171/65536 : ℝ))) 7 (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8171/65536 : ℝ)) hmem 8 (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8171/65536 : ℝ))) hcmem 8 (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8171/65536 : ℝ)) (992252872607/1000000000000 : ℝ) (99225287261/100000000000 : ℝ) (249744115969/500000000000 : ℝ) (124872057987/250000000000 : ℝ) (395360044633/500000000000 : ℝ) (395360044643/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0168_exp_lower
  have heNumeric : (1027461706329/500000000000 : ℝ)/4 ≤ Real.exp (-5328446261163/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027461706329/500000000000 : ℝ)/4 ≤ Real.exp ((4085/32768 : ℝ)-(395360044643/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4085/32768 : ℝ) (8171/65536 : ℝ) (395360044643/500000000000 : ℝ) (1027461706329/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0169; no trusted numerical premise.
theorem cover8_leaf0169_exp_radius : (199610708037253461/200000000000000000 : ℝ) ≤ Real.exp ((-2043/131072 : ℝ)/8) ∧ Real.exp ((-2043/131072 : ℝ)/8) ≤ (499026770093133653/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2043/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0169_exp_lower : (920114644022169319/1000000000000000000 : ℝ) ≤ Real.exp ((-2131379293057/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131379293057/3200000000000 : ℝ)/8) ≤ (23002866100554233/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131379293057/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0169_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054922906253/1000000000000 : ℝ) ≤ 4*Real.exp (8171/65536 : ℝ)*Real.exp (-mu (radius 8 (2043/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054922906253/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2043/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0169_exp_radius
  have hrNumeric : (3076668729/3125000000 : ℝ) ≤ Real.exp (-2043/131072 : ℝ) ∧ Real.exp (-2043/131072 : ℝ) ≤ (984533993281/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (3076668729/3125000000 : ℝ) ≤ (radius 8 (2043/16384 : ℝ)) ∧ (radius 8 (2043/16384 : ℝ)) ≤ (984533993281/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2043/16384 : ℝ)) (3076668729/3125000000 : ℝ) (984533993281/1000000000000 : ℝ) (21899206633/125000000000 : ℝ) (175193653071/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2043/16384 : ℝ)) (3076668729/3125000000 : ℝ) (984533993281/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2043/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (3076668729/3125000000 : ℝ) (984533993281/1000000000000 : ℝ) (6201668729/6250000000 : ℝ) (992266996641/1000000000000 : ℝ) (198447372699/200000000000 : ℝ) (992236863497/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2043/16384 : ℝ)) 1 (6201668729/6250000000 : ℝ) (992266996641/1000000000000 : ℝ) (198447372699/200000000000 : ℝ) (992236863497/1000000000000 : ℝ) (992251930067/1000000000000 : ℝ) (992251930069/1000000000000 : ℝ) (992251929953/1000000000000 : ℝ) (198450385991/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2043/16384 : ℝ)) 2 (992251930067/1000000000000 : ℝ) (992251930069/1000000000000 : ℝ) (992251929953/1000000000000 : ℝ) (198450385991/200000000000 : ℝ) (99225193001/100000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2043/16384 : ℝ)) 3 (99225193001/100000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2043/16384 : ℝ)) 4 (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2043/16384 : ℝ)) 5 (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2043/16384 : ℝ)) 6 (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2043/16384 : ℝ)) 7 (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2043/16384 : ℝ))) (21899206633/125000000000 : ℝ) (175193653071/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2043/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (21899206633/125000000000 : ℝ) (175193653071/1000000000000 : ℝ) (146899206633/250000000000 : ℝ) (73449603317/125000000000 : ℝ) (52320176119/125000000000 : ℝ) (418561408961/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2043/16384 : ℝ))) 1 (146899206633/250000000000 : ℝ) (73449603317/125000000000 : ℝ) (52320176119/125000000000 : ℝ) (418561408961/1000000000000 : ℝ) (251539558871/500000000000 : ℝ) (503079117749/1000000000000 : ℝ) (495928780783/1000000000000 : ℝ) (495928780791/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2043/16384 : ℝ))) 2 (251539558871/500000000000 : ℝ) (503079117749/1000000000000 : ℝ) (495928780783/1000000000000 : ℝ) (495928780791/1000000000000 : ℝ) (249751974631/500000000000 : ℝ) (49950394927/100000000000 : ℝ) (19979646183/40000000000 : ℝ) (62436394323/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2043/16384 : ℝ))) 3 (249751974631/500000000000 : ℝ) (49950394927/100000000000 : ℝ) (19979646183/40000000000 : ℝ) (62436394323/125000000000 : ℝ) (249748775959/500000000000 : ℝ) (499497551927/1000000000000 : ℝ) (499497551877/1000000000000 : ℝ) (499497551887/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2043/16384 : ℝ))) 4 (249748775959/500000000000 : ℝ) (499497551927/1000000000000 : ℝ) (499497551877/1000000000000 : ℝ) (499497551887/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2043/16384 : ℝ))) 5 (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2043/16384 : ℝ))) 6 (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2043/16384 : ℝ))) 7 (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2043/16384 : ℝ)) hmem 8 (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2043/16384 : ℝ))) hcmem 8 (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2043/16384 : ℝ)) (992251930009/1000000000000 : ℝ) (248062982503/250000000000 : ℝ) (499497551897/1000000000000 : ℝ) (499497551907/1000000000000 : ℝ) (79073559449/100000000000 : ℝ) (79073559451/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0169_exp_lower
  have heNumeric : (2054922906253/1000000000000 : ℝ)/4 ≤ Real.exp (-2131379293057/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054922906253/1000000000000 : ℝ)/4 ≤ Real.exp ((8171/65536 : ℝ)-(79073559451/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8171/65536 : ℝ) (2043/16384 : ℝ) (79073559451/100000000000 : ℝ) (2054922906253/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0170; no trusted numerical premise.
theorem cover8_leaf0170_exp_radius : (998053302231788753/1000000000000000000 : ℝ) ≤ Real.exp ((-8173/524288 : ℝ)/8) ∧ Real.exp ((-8173/524288 : ℝ)/8) ≤ (499026651115894377/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8173/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0170_exp_lower : (184022923165328769/200000000000000000 : ℝ) ≤ Real.exp ((-2664225096913/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664225096913/4000000000000 : ℝ)/8) ≤ (460057307913321923/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664225096913/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0170_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054922402493/1000000000000 : ℝ) ≤ 4*Real.exp (2043/16384 : ℝ)*Real.exp (-mu (radius 8 (8173/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054922402493/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8173/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0170_exp_radius
  have hrNumeric : (123066514429/125000000000 : ℝ) ≤ Real.exp (-8173/524288 : ℝ) ∧ Real.exp (-8173/524288 : ℝ) ≤ (984532115433/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123066514429/125000000000 : ℝ) ≤ (radius 8 (8173/65536 : ℝ)) ∧ (radius 8 (8173/65536 : ℝ)) ≤ (984532115433/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8173/65536 : ℝ)) (123066514429/125000000000 : ℝ) (984532115433/1000000000000 : ℝ) (8760210283/50000000000 : ℝ) (87602102833/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8173/65536 : ℝ)) (123066514429/125000000000 : ℝ) (984532115433/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8173/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123066514429/125000000000 : ℝ) (984532115433/1000000000000 : ℝ) (248066514429/250000000000 : ℝ) (992266057717/1000000000000 : ℝ) (39689436689/40000000000 : ℝ) (496117958613/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8173/65536 : ℝ)) 1 (248066514429/250000000000 : ℝ) (992266057717/1000000000000 : ℝ) (39689436689/40000000000 : ℝ) (496117958613/500000000000 : ℝ) (99225098747/100000000000 : ℝ) (62015686717/62500000000 : ℝ) (248062746839/250000000000 : ℝ) (496125493679/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8173/65536 : ℝ)) 2 (99225098747/100000000000 : ℝ) (62015686717/62500000000 : ℝ) (248062746839/250000000000 : ℝ) (496125493679/500000000000 : ℝ) (992250987413/1000000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8173/65536 : ℝ)) 3 (992250987413/1000000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8173/65536 : ℝ)) 4 (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8173/65536 : ℝ)) 5 (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8173/65536 : ℝ)) 6 (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8173/65536 : ℝ)) 7 (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8173/65536 : ℝ))) (8760210283/50000000000 : ℝ) (87602102833/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8173/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8760210283/50000000000 : ℝ) (87602102833/500000000000 : ℝ) (58760210283/100000000000 : ℝ) (587602102833/1000000000000 : ℝ) (209287007277/500000000000 : ℝ) (209287007281/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8173/65536 : ℝ))) 1 (58760210283/100000000000 : ℝ) (587602102833/1000000000000 : ℝ) (209287007277/500000000000 : ℝ) (209287007281/500000000000 : ℝ) (125772014673/250000000000 : ℝ) (251544029349/500000000000 : ℝ) (495938475157/1000000000000 : ℝ) (123984618791/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8173/65536 : ℝ))) 2 (125772014673/250000000000 : ℝ) (251544029349/500000000000 : ℝ) (495938475157/1000000000000 : ℝ) (123984618791/250000000000 : ℝ) (124878316731/250000000000 : ℝ) (499513266931/1000000000000 : ℝ) (124875118793/250000000000 : ℝ) (499500475179/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8173/65536 : ℝ))) 3 (124878316731/250000000000 : ℝ) (499513266931/1000000000000 : ℝ) (124875118793/250000000000 : ℝ) (499500475179/1000000000000 : ℝ) (62438358881/125000000000 : ℝ) (99901374211/200000000000 : ℝ) (499506871007/1000000000000 : ℝ) (99901374203/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8173/65536 : ℝ))) 4 (62438358881/125000000000 : ℝ) (99901374211/200000000000 : ℝ) (499506871007/1000000000000 : ℝ) (99901374203/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8173/65536 : ℝ))) 5 (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8173/65536 : ℝ))) 6 (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8173/65536 : ℝ))) 7 (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8173/65536 : ℝ)) hmem 8 (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8173/65536 : ℝ))) hcmem 8 (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8173/65536 : ℝ)) (248062746853/250000000000 : ℝ) (198450197483/200000000000 : ℝ) (499506871027/1000000000000 : ℝ) (99901374207/200000000000 : ℝ) (790751098431/1000000000000 : ℝ) (790751098447/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0170_exp_lower
  have heNumeric : (2054922402493/1000000000000 : ℝ)/4 ≤ Real.exp (-2664225096913/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054922402493/1000000000000 : ℝ)/4 ≤ Real.exp ((2043/16384 : ℝ)-(790751098447/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2043/16384 : ℝ) (8173/65536 : ℝ) (790751098447/1000000000000 : ℝ) (2054922402493/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0171; no trusted numerical premise.
theorem cover8_leaf0171_exp_radius : (499026532138683467/500000000000000000 : ℝ) ≤ Real.exp ((-4087/262144 : ℝ)/8) ∧ Real.exp ((-4087/262144 : ℝ)/8) ≤ (199610612855473387/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4087/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0171_exp_lower : (230028646944814421/250000000000000000 : ℝ) ≤ Real.exp ((-10656904289411/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656904289411/16000000000000 : ℝ)/8) ≤ (184022917555851537/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656904289411/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0171_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102746095069/50000000000 : ℝ) ≤ 4*Real.exp (8173/65536 : ℝ)*Real.exp (-mu (radius 8 (4087/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (102746095069/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4087/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0171_exp_radius
  have hrNumeric : (246132559397/250000000000 : ℝ) ≤ Real.exp (-4087/262144 : ℝ) ∧ Real.exp (-4087/262144 : ℝ) ≤ (984530237589/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246132559397/250000000000 : ℝ) ≤ (radius 8 (4087/32768 : ℝ)) ∧ (radius 8 (4087/32768 : ℝ)) ≤ (984530237589/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4087/32768 : ℝ)) (246132559397/250000000000 : ℝ) (984530237589/1000000000000 : ℝ) (175214757577/1000000000000 : ℝ) (10950922349/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4087/32768 : ℝ)) (246132559397/250000000000 : ℝ) (984530237589/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4087/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246132559397/250000000000 : ℝ) (984530237589/1000000000000 : ℝ) (496132559397/500000000000 : ℝ) (198453023759/200000000000 : ℝ) (198446994191/200000000000 : ℝ) (992234970957/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4087/32768 : ℝ)) 1 (496132559397/500000000000 : ℝ) (198453023759/200000000000 : ℝ) (198446994191/200000000000 : ℝ) (992234970957/1000000000000 : ℝ) (496125022437/500000000000 : ℝ) (248062511219/250000000000 : ℝ) (24806251119/25000000000 : ℝ) (496125022381/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4087/32768 : ℝ)) 2 (496125022437/500000000000 : ℝ) (248062511219/250000000000 : ℝ) (24806251119/25000000000 : ℝ) (496125022381/500000000000 : ℝ) (992250044817/1000000000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4087/32768 : ℝ)) 3 (992250044817/1000000000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4087/32768 : ℝ)) 4 (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4087/32768 : ℝ)) 5 (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4087/32768 : ℝ)) 6 (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4087/32768 : ℝ)) 7 (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4087/32768 : ℝ))) (175214757577/1000000000000 : ℝ) (10950922349/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4087/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175214757577/1000000000000 : ℝ) (10950922349/62500000000 : ℝ) (146901844697/250000000000 : ℝ) (73450922349/125000000000 : ℝ) (83717323793/200000000000 : ℝ) (209293309487/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4087/32768 : ℝ))) 1 (146901844697/250000000000 : ℝ) (73450922349/125000000000 : ℝ) (83717323793/200000000000 : ℝ) (209293309487/500000000000 : ℝ) (125774249719/250000000000 : ℝ) (503096998883/1000000000000 : ℝ) (123987042157/250000000000 : ℝ) (123987042159/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4087/32768 : ℝ))) 2 (125774249719/250000000000 : ℝ) (503096998883/1000000000000 : ℝ) (123987042157/250000000000 : ℝ) (123987042159/250000000000 : ℝ) (62440322969/125000000000 : ℝ) (6244032297/12500000000 : ℝ) (499509794933/1000000000000 : ℝ) (249754897471/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4087/32768 : ℝ))) 3 (62440322969/125000000000 : ℝ) (6244032297/12500000000 : ℝ) (499509794933/1000000000000 : ℝ) (249754897471/500000000000 : ℝ) (249758094671/500000000000 : ℝ) (499516189351/1000000000000 : ℝ) (499516189301/1000000000000 : ℝ) (499516189311/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4087/32768 : ℝ))) 4 (249758094671/500000000000 : ℝ) (499516189351/1000000000000 : ℝ) (499516189301/1000000000000 : ℝ) (499516189311/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4087/32768 : ℝ))) 5 (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4087/32768 : ℝ))) 6 (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4087/32768 : ℝ))) 7 (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4087/32768 : ℝ)) hmem 8 (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4087/32768 : ℝ))) hcmem 8 (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4087/32768 : ℝ)) (62015627801/62500000000 : ℝ) (992250044819/1000000000000 : ℝ) (499516189321/1000000000000 : ℝ) (499516189331/1000000000000 : ℝ) (197691650269/250000000000 : ℝ) (98845825137/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0171_exp_lower
  have heNumeric : (102746095069/50000000000 : ℝ)/4 ≤ Real.exp (-10656904289411/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102746095069/50000000000 : ℝ)/4 ≤ Real.exp ((8173/65536 : ℝ)-(98845825137/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8173/65536 : ℝ) (4087/32768 : ℝ) (98845825137/125000000000 : ℝ) (102746095069/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0172; no trusted numerical premise.
theorem cover8_leaf0172_exp_radius : (998052826323001847/1000000000000000000 : ℝ) ≤ Real.exp ((-8175/524288 : ℝ)/8) ∧ Real.exp ((-8175/524288 : ℝ)/8) ≤ (124756603290375231/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8175/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0172_exp_lower : (920114559879665779/1000000000000000000 : ℝ) ≤ Real.exp ((-1065690817061/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065690817061/1600000000000 : ℝ)/8) ≤ (46005727993983289/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065690817061/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0172_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513730350727/250000000000 : ℝ) ≤ 4*Real.exp (4087/32768 : ℝ)*Real.exp (-mu (radius 8 (8175/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513730350727/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8175/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0172_exp_radius
  have hrNumeric : (984528359747/1000000000000 : ℝ) ≤ Real.exp (-8175/524288 : ℝ) ∧ Real.exp (-8175/524288 : ℝ) ≤ (246132089937/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984528359747/1000000000000 : ℝ) ≤ (radius 8 (8175/65536 : ℝ)) ∧ (radius 8 (8175/65536 : ℝ)) ≤ (246132089937/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8175/65536 : ℝ)) (984528359747/1000000000000 : ℝ) (246132089937/250000000000 : ℝ) (87612654411/500000000000 : ℝ) (175225308829/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8175/65536 : ℝ)) (984528359747/1000000000000 : ℝ) (246132089937/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8175/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984528359747/1000000000000 : ℝ) (246132089937/250000000000 : ℝ) (992264179873/1000000000000 : ℝ) (496132089937/500000000000 : ℝ) (992234024687/1000000000000 : ℝ) (62014626543/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8175/65536 : ℝ)) 1 (992264179873/1000000000000 : ℝ) (496132089937/500000000000 : ℝ) (992234024687/1000000000000 : ℝ) (62014626543/62500000000 : ℝ) (24806227557/25000000000 : ℝ) (992249102281/1000000000000 : ℝ) (198449820433/200000000000 : ℝ) (992249102167/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8175/65536 : ℝ)) 2 (24806227557/25000000000 : ℝ) (992249102281/1000000000000 : ℝ) (198449820433/200000000000 : ℝ) (992249102167/1000000000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8175/65536 : ℝ)) 3 (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8175/65536 : ℝ)) 4 (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8175/65536 : ℝ)) 5 (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8175/65536 : ℝ)) 6 (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8175/65536 : ℝ)) 7 (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8175/65536 : ℝ))) (87612654411/500000000000 : ℝ) (175225308829/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8175/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87612654411/500000000000 : ℝ) (175225308829/1000000000000 : ℝ) (587612654411/1000000000000 : ℝ) (117522530883/200000000000 : ℝ) (209299611097/500000000000 : ℝ) (104649805551/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8175/65536 : ℝ))) 1 (587612654411/1000000000000 : ℝ) (117522530883/200000000000 : ℝ) (209299611097/500000000000 : ℝ) (104649805551/250000000000 : ℝ) (251552969151/500000000000 : ℝ) (50310593831/100000000000 : ℝ) (495957861201/1000000000000 : ℝ) (49595786121/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8175/65536 : ℝ))) 2 (251552969151/500000000000 : ℝ) (50310593831/100000000000 : ℝ) (495957861201/1000000000000 : ℝ) (49595786121/100000000000 : ℝ) (499531899751/1000000000000 : ℝ) (6244148747/12500000000 : ℝ) (249759556933/500000000000 : ℝ) (3996152911/8000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8175/65536 : ℝ))) 3 (499531899751/1000000000000 : ℝ) (6244148747/12500000000 : ℝ) (249759556933/500000000000 : ℝ) (3996152911/8000000000 : ℝ) (62440688351/125000000000 : ℝ) (249762753409/500000000000 : ℝ) (499525506767/1000000000000 : ℝ) (499525506777/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8175/65536 : ℝ))) 4 (62440688351/125000000000 : ℝ) (249762753409/500000000000 : ℝ) (499525506767/1000000000000 : ℝ) (499525506777/1000000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8175/65536 : ℝ))) 5 (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8175/65536 : ℝ))) 6 (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8175/65536 : ℝ))) 7 (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8175/65536 : ℝ)) hmem 8 (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8175/65536 : ℝ))) hcmem 8 (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8175/65536 : ℝ)) (496124551111/500000000000 : ℝ) (62015568889/62500000000 : ℝ) (499525506787/1000000000000 : ℝ) (249762753399/500000000000 : ℝ) (19769552561/25000000000 : ℝ) (39539105123/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0172_exp_lower
  have heNumeric : (513730350727/250000000000 : ℝ)/4 ≤ Real.exp (-1065690817061/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513730350727/250000000000 : ℝ)/4 ≤ Real.exp ((4087/32768 : ℝ)-(39539105123/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4087/32768 : ℝ) (8175/65536 : ℝ) (39539105123/50000000000 : ℝ) (513730350727/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0173; no trusted numerical premise.
theorem cover8_leaf0173_exp_radius : (998052588368693493/1000000000000000000 : ℝ) ≤ Real.exp ((-511/32768 : ℝ)/8) ∧ Real.exp ((-511/32768 : ℝ)/8) ≤ (499026294184346747/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-511/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0173_exp_lower : (46005726606450913/50000000000000000 : ℝ) ≤ Real.exp ((-10656912031089/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656912031089/16000000000000 : ℝ)/8) ≤ (920114532129018261/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656912031089/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0173_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256865113387/125000000000 : ℝ) ≤ 4*Real.exp (8175/65536 : ℝ)*Real.exp (-mu (radius 8 (511/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (256865113387/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (511/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0173_exp_radius
  have hrNumeric : (98452648191/100000000000 : ℝ) ≤ Real.exp (-511/32768 : ℝ) ∧ Real.exp (-511/32768 : ℝ) ≤ (984526481911/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98452648191/100000000000 : ℝ) ≤ (radius 8 (511/4096 : ℝ)) ∧ (radius 8 (511/4096 : ℝ)) ≤ (984526481911/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (511/4096 : ℝ)) (98452648191/100000000000 : ℝ) (984526481911/1000000000000 : ℝ) (175235859389/1000000000000 : ℝ) (43808964849/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (511/4096 : ℝ)) (98452648191/100000000000 : ℝ) (984526481911/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (511/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98452648191/100000000000 : ℝ) (984526481911/1000000000000 : ℝ) (198452648191/200000000000 : ℝ) (248065810239/250000000000 : ℝ) (992233078419/1000000000000 : ℝ) (992233078421/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (511/4096 : ℝ)) 1 (198452648191/200000000000 : ℝ) (248065810239/250000000000 : ℝ) (992233078419/1000000000000 : ℝ) (992233078421/1000000000000 : ℝ) (992248159687/1000000000000 : ℝ) (992248159689/1000000000000 : ℝ) (248062039893/250000000000 : ℝ) (496124079787/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (511/4096 : ℝ)) 2 (992248159687/1000000000000 : ℝ) (992248159689/1000000000000 : ℝ) (248062039893/250000000000 : ℝ) (496124079787/500000000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (511/4096 : ℝ)) 3 (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (511/4096 : ℝ)) 4 (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (511/4096 : ℝ)) 5 (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (511/4096 : ℝ)) 6 (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (511/4096 : ℝ)) 7 (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (511/4096 : ℝ))) (175235859389/1000000000000 : ℝ) (43808964849/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (511/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175235859389/1000000000000 : ℝ) (43808964849/250000000000 : ℝ) (293808964847/500000000000 : ℝ) (293808964849/500000000000 : ℝ) (209305912117/500000000000 : ℝ) (418611824243/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (511/4096 : ℝ))) 1 (293808964847/500000000000 : ℝ) (293808964849/500000000000 : ℝ) (209305912117/500000000000 : ℝ) (418611824243/1000000000000 : ℝ) (125778719241/250000000000 : ℝ) (503114876971/1000000000000 : ℝ) (495967552871/1000000000000 : ℝ) (495967552879/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (511/4096 : ℝ))) 2 (125778719241/250000000000 : ℝ) (503114876971/1000000000000 : ℝ) (495967552871/1000000000000 : ℝ) (495967552879/1000000000000 : ℝ) (499541214917/1000000000000 : ℝ) (19981648597/40000000000 : ℝ) (124882107991/250000000000 : ℝ) (124882107993/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (511/4096 : ℝ))) 3 (499541214917/1000000000000 : ℝ) (19981648597/40000000000 : ℝ) (124882107991/250000000000 : ℝ) (124882107993/250000000000 : ℝ) (6244185293/12500000000 : ℝ) (499534823449/1000000000000 : ℝ) (499534823399/1000000000000 : ℝ) (31220926463/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (511/4096 : ℝ))) 4 (6244185293/12500000000 : ℝ) (499534823449/1000000000000 : ℝ) (499534823399/1000000000000 : ℝ) (31220926463/62500000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (511/4096 : ℝ))) 5 (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (511/4096 : ℝ))) 6 (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (511/4096 : ℝ))) 7 (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (511/4096 : ℝ)) hmem 8 (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (511/4096 : ℝ))) hcmem 8 (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (511/4096 : ℝ)) (992248159629/1000000000000 : ℝ) (62015509977/62500000000 : ℝ) (499534823419/1000000000000 : ℝ) (499534823429/1000000000000 : ℝ) (79079760251/100000000000 : ℝ) (790797602529/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0173_exp_lower
  have heNumeric : (256865113387/125000000000 : ℝ)/4 ≤ Real.exp (-10656912031089/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256865113387/125000000000 : ℝ)/4 ≤ Real.exp ((8175/65536 : ℝ)-(790797602529/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8175/65536 : ℝ) (511/4096 : ℝ) (790797602529/1000000000000 : ℝ) (256865113387/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0174; no trusted numerical premise.
theorem cover8_leaf0174_exp_radius : (62378271900902617/62500000000000000 : ℝ) ≤ Real.exp ((-8177/524288 : ℝ)/8) ∧ Real.exp ((-8177/524288 : ℝ)/8) ≤ (998052350414441873/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8177/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0174_exp_lower : (920114504526394999/1000000000000000000 : ℝ) ≤ Real.exp ((-41628577621/62500000000 : ℝ)/8) ∧ Real.exp ((-41628577621/62500000000 : ℝ)/8) ≤ (184022900905279/200000000000000 : ℝ) := by
  have h := exp_small_bounds ((-41628577621/62500000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0174_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205492041393/100000000000 : ℝ) ≤ 4*Real.exp (511/4096 : ℝ)*Real.exp (-mu (radius 8 (8177/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205492041393/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8177/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0174_exp_radius
  have hrNumeric : (984524604077/1000000000000 : ℝ) ≤ Real.exp (-8177/524288 : ℝ) ∧ Real.exp (-8177/524288 : ℝ) ≤ (492262302039/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984524604077/1000000000000 : ℝ) ≤ (radius 8 (8177/65536 : ℝ)) ∧ (radius 8 (8177/65536 : ℝ)) ≤ (492262302039/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8177/65536 : ℝ)) (984524604077/1000000000000 : ℝ) (492262302039/500000000000 : ℝ) (87623204639/500000000000 : ℝ) (35049281857/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8177/65536 : ℝ)) (984524604077/1000000000000 : ℝ) (492262302039/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8177/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984524604077/1000000000000 : ℝ) (492262302039/500000000000 : ℝ) (496131151019/500000000000 : ℝ) (992262302039/1000000000000 : ℝ) (992232132153/1000000000000 : ℝ) (496116066077/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8177/65536 : ℝ)) 1 (496131151019/500000000000 : ℝ) (992262302039/1000000000000 : ℝ) (992232132153/1000000000000 : ℝ) (496116066077/500000000000 : ℝ) (198449443419/200000000000 : ℝ) (992247217097/1000000000000 : ℝ) (49612360849/50000000000 : ℝ) (496123608491/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8177/65536 : ℝ)) 2 (198449443419/200000000000 : ℝ) (992247217097/1000000000000 : ℝ) (49612360849/50000000000 : ℝ) (496123608491/500000000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8177/65536 : ℝ)) 3 (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8177/65536 : ℝ)) 4 (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8177/65536 : ℝ)) 5 (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8177/65536 : ℝ)) 6 (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8177/65536 : ℝ)) 7 (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8177/65536 : ℝ))) (87623204639/500000000000 : ℝ) (35049281857/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8177/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87623204639/500000000000 : ℝ) (35049281857/200000000000 : ℝ) (587623204639/1000000000000 : ℝ) (587623204643/1000000000000 : ℝ) (83724885017/200000000000 : ℝ) (209312212547/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8177/65536 : ℝ))) 1 (587623204639/1000000000000 : ℝ) (587623204643/1000000000000 : ℝ) (83724885017/200000000000 : ℝ) (209312212547/500000000000 : ℝ) (251561907431/500000000000 : ℝ) (503123814869/1000000000000 : ℝ) (495977243639/1000000000000 : ℝ) (495977243647/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8177/65536 : ℝ))) 2 (251561907431/500000000000 : ℝ) (503123814869/1000000000000 : ℝ) (495977243639/1000000000000 : ℝ) (495977243647/1000000000000 : ℝ) (1998202117/4000000000 : ℝ) (249775264629/500000000000 : ℝ) (124884437307/250000000000 : ℝ) (499537749237/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8177/65536 : ℝ))) 3 (1998202117/4000000000 : ℝ) (249775264629/500000000000 : ℝ) (124884437307/250000000000 : ℝ) (499537749237/1000000000000 : ℝ) (499544139239/1000000000000 : ℝ) (31221508703/62500000000 : ℝ) (249772069599/500000000000 : ℝ) (499544139207/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8177/65536 : ℝ))) 4 (499544139239/1000000000000 : ℝ) (31221508703/62500000000 : ℝ) (249772069599/500000000000 : ℝ) (499544139207/1000000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8177/65536 : ℝ))) 5 (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8177/65536 : ℝ))) 6 (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8177/65536 : ℝ))) 7 (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8177/65536 : ℝ)) hmem 8 (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8177/65536 : ℝ))) hcmem 8 (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8177/65536 : ℝ)) (992247217037/1000000000000 : ℝ) (12403090213/12500000000 : ℝ) (249772069609/500000000000 : ℝ) (124886034807/250000000000 : ℝ) (790813101291/1000000000000 : ℝ) (790813101311/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0174_exp_lower
  have heNumeric : (205492041393/100000000000 : ℝ)/4 ≤ Real.exp (-41628577621/62500000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205492041393/100000000000 : ℝ)/4 ≤ Real.exp ((511/4096 : ℝ)-(790813101311/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (511/4096 : ℝ) (8177/65536 : ℝ) (790813101311/1000000000000 : ℝ) (205492041393/100000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0150_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0150_certificate
#check SmaleRate.Proofs.cover8_leaf0151_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0151_certificate
#check SmaleRate.Proofs.cover8_leaf0152_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0152_certificate
#check SmaleRate.Proofs.cover8_leaf0153_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0153_certificate
#check SmaleRate.Proofs.cover8_leaf0154_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0154_certificate
#check SmaleRate.Proofs.cover8_leaf0155_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0155_certificate
#check SmaleRate.Proofs.cover8_leaf0156_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0156_certificate
#check SmaleRate.Proofs.cover8_leaf0157_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0157_certificate
#check SmaleRate.Proofs.cover8_leaf0158_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0158_certificate
#check SmaleRate.Proofs.cover8_leaf0159_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0159_certificate
#check SmaleRate.Proofs.cover8_leaf0160_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0160_certificate
#check SmaleRate.Proofs.cover8_leaf0161_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0161_certificate
#check SmaleRate.Proofs.cover8_leaf0162_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0162_certificate
#check SmaleRate.Proofs.cover8_leaf0163_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0163_certificate
#check SmaleRate.Proofs.cover8_leaf0164_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0164_certificate
#check SmaleRate.Proofs.cover8_leaf0165_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0165_certificate
#check SmaleRate.Proofs.cover8_leaf0166_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0166_certificate
#check SmaleRate.Proofs.cover8_leaf0167_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0167_certificate
#check SmaleRate.Proofs.cover8_leaf0168_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0168_certificate
#check SmaleRate.Proofs.cover8_leaf0169_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0169_certificate
#check SmaleRate.Proofs.cover8_leaf0170_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0170_certificate
#check SmaleRate.Proofs.cover8_leaf0171_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0171_certificate
#check SmaleRate.Proofs.cover8_leaf0172_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0172_certificate
#check SmaleRate.Proofs.cover8_leaf0173_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0173_certificate
#check SmaleRate.Proofs.cover8_leaf0174_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0174_certificate
