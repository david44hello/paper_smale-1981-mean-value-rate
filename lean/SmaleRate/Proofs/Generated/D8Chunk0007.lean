/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0175; no trusted numerical premise.
theorem cover8_leaf0175_exp_radius : (124756514057530873/125000000000000000 : ℝ) ≤ Real.exp ((-4089/262144 : ℝ)/8) ∧ Real.exp ((-4089/262144 : ℝ)/8) ≤ (199610422492049397/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4089/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0175_exp_lower : (230028619267977749/250000000000000000 : ℝ) ≤ Real.exp ((-2131383938051/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131383938051/3200000000000 : ℝ)/8) ≤ (920114477071910997/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131383938051/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0175_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205491992341/100000000000 : ℝ) ≤ 4*Real.exp (8177/65536 : ℝ)*Real.exp (-mu (radius 8 (4089/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (205491992341/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4089/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0175_exp_radius
  have hrNumeric : (984522726247/1000000000000 : ℝ) ≤ Real.exp (-4089/262144 : ℝ) ∧ Real.exp (-4089/262144 : ℝ) ≤ (123065340781/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984522726247/1000000000000 : ℝ) ≤ (radius 8 (4089/32768 : ℝ)) ∧ (radius 8 (4089/32768 : ℝ)) ≤ (123065340781/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4089/32768 : ℝ)) (984522726247/1000000000000 : ℝ) (123065340781/125000000000 : ℝ) (35051391699/200000000000 : ℝ) (87628479251/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4089/32768 : ℝ)) (984522726247/1000000000000 : ℝ) (123065340781/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4089/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984522726247/1000000000000 : ℝ) (123065340781/125000000000 : ℝ) (992261363123/1000000000000 : ℝ) (248065340781/250000000000 : ℝ) (992231185887/1000000000000 : ℝ) (31007224559/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4089/32768 : ℝ)) 1 (992261363123/1000000000000 : ℝ) (248065340781/250000000000 : ℝ) (992231185887/1000000000000 : ℝ) (31007224559/31250000000 : ℝ) (198449254901/200000000000 : ℝ) (496123137253/500000000000 : ℝ) (99224627439/100000000000 : ℝ) (124030784299/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4089/32768 : ℝ)) 2 (198449254901/200000000000 : ℝ) (496123137253/500000000000 : ℝ) (99224627439/100000000000 : ℝ) (124030784299/125000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4089/32768 : ℝ)) 3 (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4089/32768 : ℝ)) 4 (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4089/32768 : ℝ)) 5 (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4089/32768 : ℝ)) 6 (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4089/32768 : ℝ)) 7 (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4089/32768 : ℝ))) (35051391699/200000000000 : ℝ) (87628479251/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4089/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35051391699/200000000000 : ℝ) (87628479251/500000000000 : ℝ) (587628479247/1000000000000 : ℝ) (587628479251/1000000000000 : ℝ) (209318512377/500000000000 : ℝ) (418637024763/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4089/32768 : ℝ))) 1 (587628479247/1000000000000 : ℝ) (587628479251/1000000000000 : ℝ) (209318512377/500000000000 : ℝ) (418637024763/1000000000000 : ℝ) (31445797/62500000 : ℝ) (503132752007/1000000000000 : ℝ) (49598693351/100000000000 : ℝ) (247993466759/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4089/32768 : ℝ))) 2 (31445797/62500000 : ℝ) (503132752007/1000000000000 : ℝ) (49598693351/100000000000 : ℝ) (247993466759/500000000000 : ℝ) (99911968551/200000000000 : ℝ) (499559842763/1000000000000 : ℝ) (499547065663/1000000000000 : ℝ) (499547065671/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4089/32768 : ℝ))) 3 (99911968551/200000000000 : ℝ) (499559842763/1000000000000 : ℝ) (499547065663/1000000000000 : ℝ) (499547065671/1000000000000 : ℝ) (499553454209/1000000000000 : ℝ) (499553454217/1000000000000 : ℝ) (62444181771/125000000000 : ℝ) (499553454177/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4089/32768 : ℝ))) 4 (499553454209/1000000000000 : ℝ) (499553454217/1000000000000 : ℝ) (62444181771/125000000000 : ℝ) (499553454177/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4089/32768 : ℝ))) 5 (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4089/32768 : ℝ))) 6 (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4089/32768 : ℝ))) 7 (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4089/32768 : ℝ)) hmem 8 (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4089/32768 : ℝ))) hcmem 8 (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4089/32768 : ℝ)) (992246274447/1000000000000 : ℝ) (992246274449/1000000000000 : ℝ) (124888363547/250000000000 : ℝ) (499553454197/1000000000000 : ℝ) (790828598789/1000000000000 : ℝ) (158165719761/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0175_exp_lower
  have heNumeric : (205491992341/100000000000 : ℝ)/4 ≤ Real.exp (-2131383938051/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205491992341/100000000000 : ℝ)/4 ≤ Real.exp ((8177/65536 : ℝ)-(158165719761/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8177/65536 : ℝ) (4089/32768 : ℝ) (158165719761/200000000000 : ℝ) (205491992341/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0176; no trusted numerical premise.
theorem cover8_leaf0176_exp_radius : (249512968626527207/250000000000000000 : ℝ) ≤ Real.exp ((-8179/524288 : ℝ)/8) ∧ Real.exp ((-8179/524288 : ℝ)/8) ≤ (998051874506108829/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8179/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0176_exp_lower : (36804577990618049/40000000000000000 : ℝ) ≤ Real.exp ((-5328461744471/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328461744471/8000000000000 : ℝ)/8) ≤ (460057224882725613/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328461744471/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0176_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128432464721/62500000000 : ℝ) ≤ 4*Real.exp (4089/32768 : ℝ)*Real.exp (-mu (radius 8 (8179/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (128432464721/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8179/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0176_exp_radius
  have hrNumeric : (984520848421/1000000000000 : ℝ) ≤ Real.exp (-8179/524288 : ℝ) ∧ Real.exp (-8179/524288 : ℝ) ≤ (492260424211/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984520848421/1000000000000 : ℝ) ≤ (radius 8 (8179/65536 : ℝ)) ∧ (radius 8 (8179/65536 : ℝ)) ≤ (492260424211/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8179/65536 : ℝ)) (984520848421/1000000000000 : ℝ) (492260424211/500000000000 : ℝ) (35053501407/200000000000 : ℝ) (87633753521/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8179/65536 : ℝ)) (984520848421/1000000000000 : ℝ) (492260424211/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8179/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984520848421/1000000000000 : ℝ) (492260424211/500000000000 : ℝ) (99226042421/100000000000 : ℝ) (992260424211/1000000000000 : ℝ) (496115119811/500000000000 : ℝ) (992230239623/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8179/65536 : ℝ)) 1 (99226042421/100000000000 : ℝ) (992260424211/1000000000000 : ℝ) (496115119811/500000000000 : ℝ) (992230239623/1000000000000 : ℝ) (248061332979/250000000000 : ℝ) (992245331917/1000000000000 : ℝ) (992245331801/1000000000000 : ℝ) (992245331803/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8179/65536 : ℝ)) 2 (248061332979/250000000000 : ℝ) (992245331917/1000000000000 : ℝ) (992245331801/1000000000000 : ℝ) (992245331803/1000000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8179/65536 : ℝ)) 3 (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8179/65536 : ℝ)) 4 (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8179/65536 : ℝ)) 5 (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8179/65536 : ℝ)) 6 (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8179/65536 : ℝ)) 7 (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8179/65536 : ℝ))) (35053501407/200000000000 : ℝ) (87633753521/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8179/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35053501407/200000000000 : ℝ) (87633753521/500000000000 : ℝ) (587633753517/1000000000000 : ℝ) (587633753521/1000000000000 : ℝ) (83729924647/200000000000 : ℝ) (104662405811/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8179/65536 : ℝ))) 1 (587633753517/1000000000000 : ℝ) (587633753521/1000000000000 : ℝ) (83729924647/200000000000 : ℝ) (104662405811/250000000000 : ℝ) (62892711047/125000000000 : ℝ) (503141688383/1000000000000 : ℝ) (247998311239/500000000000 : ℝ) (247998311243/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8179/65536 : ℝ))) 2 (62892711047/125000000000 : ℝ) (503141688383/1000000000000 : ℝ) (247998311239/500000000000 : ℝ) (247998311243/500000000000 : ℝ) (499569155427/1000000000000 : ℝ) (99913831087/200000000000 : ℝ) (31222273829/62500000000 : ℝ) (499556381273/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8179/65536 : ℝ))) 3 (499569155427/1000000000000 : ℝ) (99913831087/200000000000 : ℝ) (31222273829/62500000000 : ℝ) (499556381273/1000000000000 : ℝ) (99912553669/200000000000 : ℝ) (249781384177/500000000000 : ℝ) (31222673019/62500000000 : ℝ) (249781384157/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8179/65536 : ℝ))) 4 (99912553669/200000000000 : ℝ) (249781384177/500000000000 : ℝ) (31222673019/62500000000 : ℝ) (249781384157/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8179/65536 : ℝ))) 5 (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8179/65536 : ℝ))) 6 (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8179/65536 : ℝ))) 7 (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8179/65536 : ℝ)) hmem 8 (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8179/65536 : ℝ))) hcmem 8 (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8179/65536 : ℝ)) (496122665929/500000000000 : ℝ) (49612266593/50000000000 : ℝ) (124890692081/250000000000 : ℝ) (249781384167/500000000000 : ℝ) (790844094993/1000000000000 : ℝ) (197711023753/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0176_exp_lower
  have heNumeric : (128432464721/62500000000 : ℝ)/4 ≤ Real.exp (-5328461744471/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128432464721/62500000000 : ℝ)/4 ≤ Real.exp ((4089/32768 : ℝ)-(197711023753/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4089/32768 : ℝ) (8179/65536 : ℝ) (197711023753/250000000000 : ℝ) (128432464721/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0177; no trusted numerical premise.
theorem cover8_leaf0177_exp_radius : (199610327310405481/200000000000000000 : ℝ) ≤ Real.exp ((-2045/131072 : ℝ)/8) ∧ Real.exp ((-2045/131072 : ℝ)/8) ≤ (499025818276013703/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2045/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0177_exp_lower : (920114422606670629/1000000000000000000 : ℝ) ≤ Real.exp ((-2131385453417/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131385453417/3200000000000 : ℝ)/8) ≤ (92011442260667063/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131385453417/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0177_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054918950299/1000000000000 : ℝ) ≤ 4*Real.exp (8179/65536 : ℝ)*Real.exp (-mu (radius 8 (2045/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054918950299/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2045/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0177_exp_radius
  have hrNumeric : (492259485299/500000000000 : ℝ) ≤ Real.exp (-2045/131072 : ℝ) ∧ Real.exp (-2045/131072 : ℝ) ≤ (984518970599/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492259485299/500000000000 : ℝ) ≤ (radius 8 (2045/16384 : ℝ)) ∧ (radius 8 (2045/16384 : ℝ)) ≤ (984518970599/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2045/16384 : ℝ)) (492259485299/500000000000 : ℝ) (984518970599/1000000000000 : ℝ) (175278054903/1000000000000 : ℝ) (175278054909/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2045/16384 : ℝ)) (492259485299/500000000000 : ℝ) (984518970599/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2045/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492259485299/500000000000 : ℝ) (984518970599/1000000000000 : ℝ) (992259485299/1000000000000 : ℝ) (9922594853/10000000000 : ℝ) (496114646679/500000000000 : ℝ) (992229293359/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2045/16384 : ℝ)) 1 (992259485299/1000000000000 : ℝ) (9922594853/10000000000 : ℝ) (496114646679/500000000000 : ℝ) (992229293359/1000000000000 : ℝ) (62015274333/62500000000 : ℝ) (99224438933/100000000000 : ℝ) (992244389213/1000000000000 : ℝ) (198448877843/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2045/16384 : ℝ)) 2 (62015274333/62500000000 : ℝ) (99224438933/100000000000 : ℝ) (992244389213/1000000000000 : ℝ) (198448877843/200000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2045/16384 : ℝ)) 3 (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2045/16384 : ℝ)) 4 (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2045/16384 : ℝ)) 5 (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2045/16384 : ℝ)) 6 (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2045/16384 : ℝ)) 7 (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2045/16384 : ℝ))) (175278054903/1000000000000 : ℝ) (175278054909/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2045/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175278054903/1000000000000 : ℝ) (175278054909/1000000000000 : ℝ) (587639027451/1000000000000 : ℝ) (117527805491/200000000000 : ℝ) (209331110267/500000000000 : ℝ) (209331110271/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2045/16384 : ℝ))) 1 (587639027451/1000000000000 : ℝ) (117527805491/200000000000 : ℝ) (209331110267/500000000000 : ℝ) (209331110271/500000000000 : ℝ) (62893827999/125000000000 : ℝ) (503150623999/1000000000000 : ℝ) (496006310549/1000000000000 : ℝ) (496006310557/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2045/16384 : ℝ))) 2 (62893827999/125000000000 : ℝ) (503150623999/1000000000000 : ℝ) (496006310549/1000000000000 : ℝ) (496006310557/1000000000000 : ℝ) (49957846727/100000000000 : ℝ) (249789233639/500000000000 : ℝ) (124891424009/250000000000 : ℝ) (99913139209/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2045/16384 : ℝ))) 3 (49957846727/100000000000 : ℝ) (249789233639/500000000000 : ℝ) (124891424009/250000000000 : ℝ) (99913139209/200000000000 : ℝ) (499572081653/1000000000000 : ℝ) (249786040831/500000000000 : ℝ) (124893020403/250000000000 : ℝ) (499572081621/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2045/16384 : ℝ))) 4 (499572081653/1000000000000 : ℝ) (249786040831/500000000000 : ℝ) (124893020403/250000000000 : ℝ) (499572081621/1000000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2045/16384 : ℝ))) 5 (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2045/16384 : ℝ))) 6 (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2045/16384 : ℝ))) 7 (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2045/16384 : ℝ)) hmem 8 (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2045/16384 : ℝ))) hcmem 8 (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2045/16384 : ℝ)) (99224438927/100000000000 : ℝ) (992244389273/1000000000000 : ℝ) (15611627551/31250000000 : ℝ) (249786040821/500000000000 : ℝ) (158171917983/200000000000 : ℝ) (158171917987/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0177_exp_lower
  have heNumeric : (2054918950299/1000000000000 : ℝ)/4 ≤ Real.exp (-2131385453417/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054918950299/1000000000000 : ℝ)/4 ≤ Real.exp ((8179/65536 : ℝ)-(158171917987/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8179/65536 : ℝ) (2045/16384 : ℝ) (158171917987/200000000000 : ℝ) (2054918950299/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0178; no trusted numerical premise.
theorem cover8_leaf0178_exp_radius : (499025699299001357/500000000000000000 : ℝ) ≤ Real.exp ((-8181/524288 : ℝ)/8) ∧ Real.exp ((-8181/524288 : ℝ)/8) ≤ (199610279719600543/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8181/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0178_exp_lower : (230028598899151081/250000000000000000 : ℝ) ≤ Real.exp ((-532846551227/800000000000 : ℝ)/8) ∧ Real.exp ((-532846551227/800000000000 : ℝ)/8) ≤ (36804575823864173/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532846551227/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0178_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372961693/25000000000 : ℝ) ≤ 4*Real.exp (2045/16384 : ℝ)*Real.exp (-mu (radius 8 (8181/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (51372961693/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8181/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0178_exp_radius
  have hrNumeric : (984517092779/1000000000000 : ℝ) ≤ Real.exp (-8181/524288 : ℝ) ∧ Real.exp (-8181/524288 : ℝ) ≤ (49225854639/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984517092779/1000000000000 : ℝ) ≤ (radius 8 (8181/65536 : ℝ)) ∧ (radius 8 (8181/65536 : ℝ)) ≤ (49225854639/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8181/65536 : ℝ)) (984517092779/1000000000000 : ℝ) (49225854639/50000000000 : ℝ) (175288602093/1000000000000 : ℝ) (1752886021/10000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8181/65536 : ℝ)) (984517092779/1000000000000 : ℝ) (49225854639/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8181/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984517092779/1000000000000 : ℝ) (49225854639/50000000000 : ℝ) (992258546389/1000000000000 : ℝ) (99225854639/100000000000 : ℝ) (198445669419/200000000000 : ℝ) (124028543387/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8181/65536 : ℝ)) 1 (992258546389/1000000000000 : ℝ) (99225854639/100000000000 : ℝ) (198445669419/200000000000 : ℝ) (124028543387/125000000000 : ℝ) (496121723371/500000000000 : ℝ) (992243446743/1000000000000 : ℝ) (992243446627/1000000000000 : ℝ) (992243446629/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8181/65536 : ℝ)) 2 (496121723371/500000000000 : ℝ) (992243446743/1000000000000 : ℝ) (992243446627/1000000000000 : ℝ) (992243446629/1000000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8181/65536 : ℝ)) 3 (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8181/65536 : ℝ)) 4 (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8181/65536 : ℝ)) 5 (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8181/65536 : ℝ)) 6 (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8181/65536 : ℝ)) 7 (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8181/65536 : ℝ))) (175288602093/1000000000000 : ℝ) (1752886021/10000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8181/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175288602093/1000000000000 : ℝ) (1752886021/10000000000 : ℝ) (293822150523/500000000000 : ℝ) (11752886021/20000000000 : ℝ) (83734963329/200000000000 : ℝ) (209337408327/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8181/65536 : ℝ))) 1 (293822150523/500000000000 : ℝ) (11752886021/20000000000 : ℝ) (83734963329/200000000000 : ℝ) (209337408327/500000000000 : ℝ) (100631911769/200000000000 : ℝ) (125789889713/250000000000 : ℝ) (248007998859/500000000000 : ℝ) (248007998863/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8181/65536 : ℝ))) 2 (100631911769/200000000000 : ℝ) (125789889713/250000000000 : ℝ) (248007998859/500000000000 : ℝ) (248007998863/500000000000 : ℝ) (499587778281/1000000000000 : ℝ) (499587778289/1000000000000 : ℝ) (19983000399/40000000000 : ℝ) (499575009983/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8181/65536 : ℝ))) 3 (499587778281/1000000000000 : ℝ) (499587778289/1000000000000 : ℝ) (19983000399/40000000000 : ℝ) (499575009983/1000000000000 : ℝ) (31223837133/62500000000 : ℝ) (62447674267/125000000000 : ℝ) (499581394087/1000000000000 : ℝ) (31223837131/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8181/65536 : ℝ))) 4 (31223837133/62500000000 : ℝ) (62447674267/125000000000 : ℝ) (499581394087/1000000000000 : ℝ) (31223837131/62500000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8181/65536 : ℝ))) 5 (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8181/65536 : ℝ))) 6 (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8181/65536 : ℝ))) 7 (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8181/65536 : ℝ)) hmem 8 (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8181/65536 : ℝ))) hcmem 8 (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8181/65536 : ℝ)) (248060861671/250000000000 : ℝ) (496121723343/500000000000 : ℝ) (499581394107/1000000000000 : ℝ) (124895348529/250000000000 : ℝ) (197718770887/250000000000 : ℝ) (158175016713/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0178_exp_lower
  have heNumeric : (51372961693/25000000000 : ℝ)/4 ≤ Real.exp (-532846551227/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372961693/25000000000 : ℝ)/4 ≤ Real.exp ((2045/16384 : ℝ)-(158175016713/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2045/16384 : ℝ) (8181/65536 : ℝ) (158175016713/200000000000 : ℝ) (51372961693/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0179; no trusted numerical premise.
theorem cover8_leaf0179_exp_radius : (998051160644034757/1000000000000000000 : ℝ) ≤ Real.exp ((-4091/262144 : ℝ)/8) ∧ Real.exp ((-4091/262144 : ℝ)/8) ≤ (499025580322017379/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4091/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0179_exp_lower : (460057184366648527/500000000000000000 : ℝ) ≤ Real.exp ((-10656934761579/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656934761579/16000000000000 : ℝ)/8) ≤ (184022873746659411/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656934761579/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0179_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513729496941/250000000000 : ℝ) ≤ 4*Real.exp (8181/65536 : ℝ)*Real.exp (-mu (radius 8 (4091/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513729496941/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4091/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0179_exp_radius
  have hrNumeric : (984515214963/1000000000000 : ℝ) ≤ Real.exp (-4091/262144 : ℝ) ∧ Real.exp (-4091/262144 : ℝ) ≤ (246128803741/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984515214963/1000000000000 : ℝ) ≤ (radius 8 (4091/32768 : ℝ)) ∧ (radius 8 (4091/32768 : ℝ)) ≤ (246128803741/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4091/32768 : ℝ)) (984515214963/1000000000000 : ℝ) (246128803741/250000000000 : ℝ) (43824787153/250000000000 : ℝ) (175299148619/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4091/32768 : ℝ)) (984515214963/1000000000000 : ℝ) (246128803741/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4091/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984515214963/1000000000000 : ℝ) (246128803741/250000000000 : ℝ) (992257607481/1000000000000 : ℝ) (496128803741/500000000000 : ℝ) (7751776569/7812500000 : ℝ) (496113700417/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4091/32768 : ℝ)) 1 (992257607481/1000000000000 : ℝ) (496128803741/500000000000 : ℝ) (7751776569/7812500000 : ℝ) (496113700417/500000000000 : ℝ) (248060626039/250000000000 : ℝ) (496121252079/500000000000 : ℝ) (992242504041/1000000000000 : ℝ) (248060626011/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4091/32768 : ℝ)) 2 (248060626039/250000000000 : ℝ) (496121252079/500000000000 : ℝ) (992242504041/1000000000000 : ℝ) (248060626011/250000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4091/32768 : ℝ)) 3 (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4091/32768 : ℝ)) 4 (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4091/32768 : ℝ)) 5 (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4091/32768 : ℝ)) 6 (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4091/32768 : ℝ)) 7 (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4091/32768 : ℝ))) (43824787153/250000000000 : ℝ) (175299148619/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4091/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43824787153/250000000000 : ℝ) (175299148619/1000000000000 : ℝ) (293824787153/500000000000 : ℝ) (58764957431/100000000000 : ℝ) (16747496463/40000000000 : ℝ) (83737482317/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4091/32768 : ℝ))) 1 (293824787153/500000000000 : ℝ) (58764957431/100000000000 : ℝ) (16747496463/40000000000 : ℝ) (83737482317/200000000000 : ℝ) (25158424647/50000000000 : ℝ) (125792123237/250000000000 : ℝ) (496025683991/1000000000000 : ℝ) (124006421/250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4091/32768 : ℝ))) 2 (25158424647/50000000000 : ℝ) (125792123237/250000000000 : ℝ) (496025683991/1000000000000 : ℝ) (124006421/250000000 : ℝ) (99919417693/200000000000 : ℝ) (249798544237/500000000000 : ℝ) (99916864617/200000000000 : ℝ) (99916864619/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4091/32768 : ℝ))) 3 (99919417693/200000000000 : ℝ) (249798544237/500000000000 : ℝ) (99916864617/200000000000 : ℝ) (99916864619/200000000000 : ℝ) (19983628231/40000000000 : ℝ) (99918141157/200000000000 : ℝ) (249795352867/500000000000 : ℝ) (31224419109/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4091/32768 : ℝ))) 4 (19983628231/40000000000 : ℝ) (99918141157/200000000000 : ℝ) (249795352867/500000000000 : ℝ) (31224419109/62500000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4091/32768 : ℝ))) 5 (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4091/32768 : ℝ))) 6 (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4091/32768 : ℝ))) 7 (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4091/32768 : ℝ)) hmem 8 (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4091/32768 : ℝ))) hcmem 8 (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4091/32768 : ℝ)) (496121252049/500000000000 : ℝ) (992242504101/1000000000000 : ℝ) (249795352877/500000000000 : ℝ) (99918141153/200000000000 : ℝ) (395445287949/500000000000 : ℝ) (790890575919/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0179_exp_lower
  have heNumeric : (513729496941/250000000000 : ℝ)/4 ≤ Real.exp (-10656934761579/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513729496941/250000000000 : ℝ)/4 ≤ Real.exp ((8181/65536 : ℝ)-(790890575919/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8181/65536 : ℝ) (4091/32768 : ℝ) (790890575919/1000000000000 : ℝ) (513729496941/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0180; no trusted numerical premise.
theorem cover8_leaf0180_exp_radius : (249512730672530883/250000000000000000 : ℝ) ≤ Real.exp ((-8183/524288 : ℝ)/8) ∧ Real.exp ((-8183/524288 : ℝ)/8) ≤ (998050922690123533/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8183/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0180_exp_lower : (920114342018934077/1000000000000000000 : ℝ) ≤ Real.exp ((-5328469238949/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328469238949/8000000000000 : ℝ)/8) ≤ (460057171009467039/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328469238949/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0180_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513729377617/250000000000 : ℝ) ≤ 4*Real.exp (4091/32768 : ℝ)*Real.exp (-mu (radius 8 (8183/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513729377617/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8183/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0180_exp_radius
  have hrNumeric : (984513337151/1000000000000 : ℝ) ≤ Real.exp (-8183/524288 : ℝ) ∧ Real.exp (-8183/524288 : ℝ) ≤ (15383020893/15625000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984513337151/1000000000000 : ℝ) ≤ (radius 8 (8183/65536 : ℝ)) ∧ (radius 8 (8183/65536 : ℝ)) ≤ (15383020893/15625000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8183/65536 : ℝ)) (984513337151/1000000000000 : ℝ) (15383020893/15625000000 : ℝ) (87654847227/500000000000 : ℝ) (175309694461/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8183/65536 : ℝ)) (984513337151/1000000000000 : ℝ) (15383020893/15625000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8183/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984513337151/1000000000000 : ℝ) (15383020893/15625000000 : ℝ) (39690266743/40000000000 : ℝ) (31008020893/31250000000 : ℝ) (992226454571/1000000000000 : ℝ) (248056613643/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8183/65536 : ℝ)) 1 (39690266743/40000000000 : ℝ) (31008020893/31250000000 : ℝ) (992226454571/1000000000000 : ℝ) (248056613643/250000000000 : ℝ) (992241561573/1000000000000 : ℝ) (496120780787/500000000000 : ℝ) (992241561457/1000000000000 : ℝ) (992241561459/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8183/65536 : ℝ)) 2 (992241561573/1000000000000 : ℝ) (496120780787/500000000000 : ℝ) (992241561457/1000000000000 : ℝ) (992241561459/1000000000000 : ℝ) (198448312303/200000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8183/65536 : ℝ)) 3 (198448312303/200000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8183/65536 : ℝ)) 4 (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8183/65536 : ℝ)) 5 (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8183/65536 : ℝ)) 6 (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8183/65536 : ℝ)) 7 (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8183/65536 : ℝ))) (87654847227/500000000000 : ℝ) (175309694461/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8183/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87654847227/500000000000 : ℝ) (175309694461/1000000000000 : ℝ) (587654847227/1000000000000 : ℝ) (587654847231/1000000000000 : ℝ) (209350002659/500000000000 : ℝ) (26168750333/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8183/65536 : ℝ))) 1 (587654847227/1000000000000 : ℝ) (587654847231/1000000000000 : ℝ) (209350002659/500000000000 : ℝ) (26168750333/62500000000 : ℝ) (15724294571/31250000000 : ℝ) (12579435657/25000000000 : ℝ) (496035369363/1000000000000 : ℝ) (496035369371/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8183/65536 : ℝ))) 2 (15724294571/31250000000 : ℝ) (12579435657/25000000000 : ℝ) (496035369363/1000000000000 : ℝ) (496035369371/1000000000000 : ℝ) (499606397817/1000000000000 : ℝ) (249803198913/500000000000 : ℝ) (499593635363/1000000000000 : ℝ) (124898408843/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8183/65536 : ℝ))) 3 (499606397817/1000000000000 : ℝ) (249803198913/500000000000 : ℝ) (499593635363/1000000000000 : ℝ) (124898408843/250000000000 : ℝ) (49960001659/100000000000 : ℝ) (499600016599/1000000000000 : ℝ) (499600016549/1000000000000 : ℝ) (499600016559/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8183/65536 : ℝ))) 4 (49960001659/100000000000 : ℝ) (499600016599/1000000000000 : ℝ) (499600016549/1000000000000 : ℝ) (499600016559/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8183/65536 : ℝ))) 5 (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8183/65536 : ℝ))) 6 (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8183/65536 : ℝ))) 7 (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8183/65536 : ℝ)) hmem 8 (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8183/65536 : ℝ))) hcmem 8 (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8183/65536 : ℝ)) (496120780757/500000000000 : ℝ) (992241561517/1000000000000 : ℝ) (499600016569/1000000000000 : ℝ) (499600016579/1000000000000 : ℝ) (790906066959/1000000000000 : ℝ) (395453033489/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0180_exp_lower
  have heNumeric : (513729377617/250000000000 : ℝ)/4 ≤ Real.exp (-5328469238949/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513729377617/250000000000 : ℝ)/4 ≤ Real.exp ((4091/32768 : ℝ)-(395453033489/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4091/32768 : ℝ) (8183/65536 : ℝ) (395453033489/500000000000 : ℝ) (513729377617/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0181; no trusted numerical premise.
theorem cover8_leaf0181_exp_radius : (998050684736269039/1000000000000000000 : ℝ) ≤ Real.exp ((-1023/65536 : ℝ)/8) ∧ Real.exp ((-1023/65536 : ℝ)/8) ≤ (12475633559203363/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1023/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0181_exp_lower : (23002857886317757/25000000000000000 : ℝ) ≤ Real.exp ((-10656942173609/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656942173609/16000000000000 : ℝ)/8) ≤ (920114315452710281/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656942173609/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0181_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054917035819/1000000000000 : ℝ) ≤ 4*Real.exp (8183/65536 : ℝ)*Real.exp (-mu (radius 8 (1023/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (2054917035819/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1023/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0181_exp_radius
  have hrNumeric : (984511459343/1000000000000 : ℝ) ≤ Real.exp (-1023/65536 : ℝ) ∧ Real.exp (-1023/65536 : ℝ) ≤ (61531966209/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984511459343/1000000000000 : ℝ) ≤ (radius 8 (1023/8192 : ℝ)) ∧ (radius 8 (1023/8192 : ℝ)) ≤ (61531966209/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1023/8192 : ℝ)) (984511459343/1000000000000 : ℝ) (61531966209/62500000000 : ℝ) (175320239619/1000000000000 : ℝ) (87660119813/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1023/8192 : ℝ)) (984511459343/1000000000000 : ℝ) (61531966209/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1023/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984511459343/1000000000000 : ℝ) (61531966209/62500000000 : ℝ) (992255729671/1000000000000 : ℝ) (124031966209/125000000000 : ℝ) (99222550831/100000000000 : ℝ) (124028188539/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1023/8192 : ℝ)) 1 (992255729671/1000000000000 : ℝ) (124031966209/125000000000 : ℝ) (99222550831/100000000000 : ℝ) (124028188539/125000000000 : ℝ) (99224061899/100000000000 : ℝ) (62015038687/62500000000 : ℝ) (7937924951/8000000000 : ℝ) (992240618877/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1023/8192 : ℝ)) 2 (99224061899/100000000000 : ℝ) (62015038687/62500000000 : ℝ) (7937924951/8000000000 : ℝ) (992240618877/1000000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1023/8192 : ℝ)) 3 (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1023/8192 : ℝ)) 4 (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1023/8192 : ℝ)) 5 (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1023/8192 : ℝ)) 6 (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1023/8192 : ℝ)) 7 (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1023/8192 : ℝ))) (175320239619/1000000000000 : ℝ) (87660119813/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1023/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175320239619/1000000000000 : ℝ) (87660119813/500000000000 : ℝ) (587660119809/1000000000000 : ℝ) (587660119813/1000000000000 : ℝ) (209356298937/500000000000 : ℝ) (104678149471/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1023/8192 : ℝ))) 1 (587660119809/1000000000000 : ℝ) (587660119813/1000000000000 : ℝ) (209356298937/500000000000 : ℝ) (104678149471/250000000000 : ℝ) (503186358841/1000000000000 : ℝ) (503186358849/1000000000000 : ℝ) (62005631729/125000000000 : ℝ) (496045053841/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1023/8192 : ℝ))) 2 (503186358841/1000000000000 : ℝ) (503186358849/1000000000000 : ℝ) (62005631729/125000000000 : ℝ) (496045053841/1000000000000 : ℝ) (15612990823/31250000000 : ℝ) (99923141269/200000000000 : ℝ) (499602946807/1000000000000 : ℝ) (499602946817/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1023/8192 : ℝ))) 3 (15612990823/31250000000 : ℝ) (99923141269/200000000000 : ℝ) (499602946807/1000000000000 : ℝ) (499602946817/1000000000000 : ℝ) (499609326571/1000000000000 : ℝ) (499609326581/1000000000000 : ℝ) (49960932653/100000000000 : ℝ) (499609326541/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1023/8192 : ℝ))) 4 (499609326571/1000000000000 : ℝ) (499609326581/1000000000000 : ℝ) (49960932653/100000000000 : ℝ) (499609326541/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1023/8192 : ℝ))) 5 (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1023/8192 : ℝ))) 6 (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1023/8192 : ℝ))) 7 (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1023/8192 : ℝ)) hmem 8 (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1023/8192 : ℝ))) hcmem 8 (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1023/8192 : ℝ)) (248060154733/250000000000 : ℝ) (198448123787/200000000000 : ℝ) (9992186531/20000000000 : ℝ) (499609326561/1000000000000 : ℝ) (98865194591/125000000000 : ℝ) (790921556749/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0181_exp_lower
  have heNumeric : (2054917035819/1000000000000 : ℝ)/4 ≤ Real.exp (-10656942173609/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054917035819/1000000000000 : ℝ)/4 ≤ Real.exp ((8183/65536 : ℝ)-(790921556749/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8183/65536 : ℝ) (1023/8192 : ℝ) (790921556749/1000000000000 : ℝ) (2054917035819/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0182; no trusted numerical premise.
theorem cover8_leaf0182_exp_radius : (998050446782471279/1000000000000000000 : ℝ) ≤ Real.exp ((-8185/524288 : ℝ)/8) ∧ Real.exp ((-8185/524288 : ℝ)/8) ≤ (12475630584780891/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8185/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0182_exp_lower : (920114289033820551/1000000000000000000 : ℝ) ≤ Real.exp ((-1332118231103/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332118231103/2000000000000 : ℝ)/8) ≤ (115014286129227569/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332118231103/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0182_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054916563803/1000000000000 : ℝ) ≤ 4*Real.exp (1023/8192 : ℝ)*Real.exp (-mu (radius 8 (8185/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054916563803/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8185/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0182_exp_radius
  have hrNumeric : (492254790769/500000000000 : ℝ) ≤ Real.exp (-8185/524288 : ℝ) ∧ Real.exp (-8185/524288 : ℝ) ≤ (984509581539/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492254790769/500000000000 : ℝ) ≤ (radius 8 (8185/65536 : ℝ)) ∧ (radius 8 (8185/65536 : ℝ)) ≤ (984509581539/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8185/65536 : ℝ)) (492254790769/500000000000 : ℝ) (984509581539/1000000000000 : ℝ) (175330784113/1000000000000 : ℝ) (4383269603/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8185/65536 : ℝ)) (492254790769/500000000000 : ℝ) (984509581539/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8185/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492254790769/500000000000 : ℝ) (984509581539/1000000000000 : ℝ) (992254790769/1000000000000 : ℝ) (99225479077/100000000000 : ℝ) (992224562051/1000000000000 : ℝ) (248056140513/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8185/65536 : ℝ)) 1 (992254790769/1000000000000 : ℝ) (99225479077/100000000000 : ℝ) (992224562051/1000000000000 : ℝ) (248056140513/250000000000 : ℝ) (99223967641/100000000000 : ℝ) (992239676411/1000000000000 : ℝ) (496119838147/500000000000 : ℝ) (124029959537/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8185/65536 : ℝ)) 2 (99223967641/100000000000 : ℝ) (992239676411/1000000000000 : ℝ) (496119838147/500000000000 : ℝ) (124029959537/125000000000 : ℝ) (15503744943/15625000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8185/65536 : ℝ)) 3 (15503744943/15625000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8185/65536 : ℝ)) 4 (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8185/65536 : ℝ)) 5 (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8185/65536 : ℝ)) 6 (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8185/65536 : ℝ)) 7 (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8185/65536 : ℝ))) (175330784113/1000000000000 : ℝ) (4383269603/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8185/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175330784113/1000000000000 : ℝ) (4383269603/25000000000 : ℝ) (73458174007/125000000000 : ℝ) (29383269603/50000000000 : ℝ) (1674900757/4000000000 : ℝ) (20936259463/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8185/65536 : ℝ))) 1 (73458174007/125000000000 : ℝ) (29383269603/50000000000 : ℝ) (1674900757/4000000000 : ℝ) (20936259463/50000000000 : ℝ) (503195290653/1000000000000 : ℝ) (25159764533/50000000000 : ℝ) (496054737407/1000000000000 : ℝ) (62006842177/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8185/65536 : ℝ))) 2 (503195290653/1000000000000 : ℝ) (25159764533/50000000000 : ℝ) (496054737407/1000000000000 : ℝ) (62006842177/125000000000 : ℝ) (49962501403/100000000000 : ℝ) (249812507019/500000000000 : ℝ) (19984490297/40000000000 : ℝ) (249806128717/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8185/65536 : ℝ))) 3 (49962501403/100000000000 : ℝ) (249812507019/500000000000 : ℝ) (19984490297/40000000000 : ℝ) (249806128717/500000000000 : ℝ) (499618635727/1000000000000 : ℝ) (62452329467/125000000000 : ℝ) (249809317843/500000000000 : ℝ) (31226164731/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8185/65536 : ℝ))) 4 (499618635727/1000000000000 : ℝ) (62452329467/125000000000 : ℝ) (249809317843/500000000000 : ℝ) (31226164731/62500000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8185/65536 : ℝ))) 5 (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8185/65536 : ℝ))) 6 (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8185/65536 : ℝ))) 7 (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8185/65536 : ℝ)) hmem 8 (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8185/65536 : ℝ))) hcmem 8 (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8185/65536 : ℝ)) (992239676351/1000000000000 : ℝ) (496119838177/500000000000 : ℝ) (249809317853/500000000000 : ℝ) (124904658929/250000000000 : ℝ) (790937045219/1000000000000 : ℝ) (790937045239/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0182_exp_lower
  have heNumeric : (2054916563803/1000000000000 : ℝ)/4 ≤ Real.exp (-1332118231103/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054916563803/1000000000000 : ℝ)/4 ≤ Real.exp ((1023/8192 : ℝ)-(790937045239/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1023/8192 : ℝ) (8185/65536 : ℝ) (790937045239/1000000000000 : ℝ) (2054916563803/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0183; no trusted numerical premise.
theorem cover8_leaf0183_exp_radius : (249512552207182563/250000000000000000 : ℝ) ≤ Real.exp ((-4093/262144 : ℝ)/8) ∧ Real.exp ((-4093/262144 : ℝ)/8) ≤ (998050208828730253/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4093/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0183_exp_lower : (46005713138170751/50000000000000000 : ℝ) ≤ Real.exp ((-10656949503383/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656949503383/16000000000000 : ℝ)/8) ≤ (920114262763415021/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656949503383/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0183_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372902361/25000000000 : ℝ) ≤ 4*Real.exp (8185/65536 : ℝ)*Real.exp (-mu (radius 8 (4093/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (51372902361/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4093/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0183_exp_radius
  have hrNumeric : (984507703737/1000000000000 : ℝ) ≤ Real.exp (-4093/262144 : ℝ) ∧ Real.exp (-4093/262144 : ℝ) ≤ (492253851869/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984507703737/1000000000000 : ℝ) ≤ (radius 8 (4093/32768 : ℝ)) ∧ (radius 8 (4093/32768 : ℝ)) ≤ (492253851869/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4093/32768 : ℝ)) (984507703737/1000000000000 : ℝ) (492253851869/500000000000 : ℝ) (17534132793/100000000000 : ℝ) (175341327937/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4093/32768 : ℝ)) (984507703737/1000000000000 : ℝ) (492253851869/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4093/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984507703737/1000000000000 : ℝ) (492253851869/500000000000 : ℝ) (248063462967/250000000000 : ℝ) (992253851869/1000000000000 : ℝ) (62013975987/62500000000 : ℝ) (496111807897/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4093/32768 : ℝ)) 1 (248063462967/250000000000 : ℝ) (992253851869/1000000000000 : ℝ) (62013975987/62500000000 : ℝ) (496111807897/500000000000 : ℝ) (99223873383/100000000000 : ℝ) (124029841729/125000000000 : ℝ) (496119366857/500000000000 : ℝ) (992238733717/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4093/32768 : ℝ)) 2 (99223873383/100000000000 : ℝ) (124029841729/125000000000 : ℝ) (496119366857/500000000000 : ℝ) (992238733717/1000000000000 : ℝ) (248059683443/250000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4093/32768 : ℝ)) 3 (248059683443/250000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4093/32768 : ℝ)) 4 (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4093/32768 : ℝ)) 5 (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4093/32768 : ℝ)) 6 (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4093/32768 : ℝ)) 7 (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4093/32768 : ℝ))) (17534132793/100000000000 : ℝ) (175341327937/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4093/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17534132793/100000000000 : ℝ) (175341327937/1000000000000 : ℝ) (117534132793/200000000000 : ℝ) (587670663969/1000000000000 : ℝ) (418737779439/1000000000000 : ℝ) (52342222431/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4093/32768 : ℝ))) 1 (117534132793/200000000000 : ℝ) (587670663969/1000000000000 : ℝ) (418737779439/1000000000000 : ℝ) (52342222431/125000000000 : ℝ) (251602110851/500000000000 : ℝ) (503204221709/1000000000000 : ℝ) (6200805251/12500000000 : ℝ) (62008052511/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4093/32768 : ℝ))) 2 (251602110851/500000000000 : ℝ) (503204221709/1000000000000 : ℝ) (6200805251/12500000000 : ℝ) (62008052511/125000000000 : ℝ) (499634320891/1000000000000 : ℝ) (499634320899/1000000000000 : ℝ) (499621567209/1000000000000 : ℝ) (499621567217/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4093/32768 : ℝ))) 3 (499634320891/1000000000000 : ℝ) (499634320899/1000000000000 : ℝ) (499621567209/1000000000000 : ℝ) (499621567217/1000000000000 : ℝ) (9992558881/20000000000 : ℝ) (249813972029/500000000000 : ℝ) (499627944009/1000000000000 : ℝ) (249813972009/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4093/32768 : ℝ))) 4 (9992558881/20000000000 : ℝ) (249813972029/500000000000 : ℝ) (499627944009/1000000000000 : ℝ) (249813972009/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4093/32768 : ℝ))) 5 (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4093/32768 : ℝ))) 6 (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4093/32768 : ℝ))) 7 (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4093/32768 : ℝ)) hmem 8 (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4093/32768 : ℝ))) hcmem 8 (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4093/32768 : ℝ)) (992238733771/1000000000000 : ℝ) (39689549351/40000000000 : ℝ) (499627944029/1000000000000 : ℝ) (249813972019/500000000000 : ℝ) (39547626621/50000000000 : ℝ) (395476266219/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0183_exp_lower
  have heNumeric : (51372902361/25000000000 : ℝ)/4 ≤ Real.exp (-10656949503383/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372902361/25000000000 : ℝ)/4 ≤ Real.exp ((8185/65536 : ℝ)-(395476266219/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8185/65536 : ℝ) (4093/32768 : ℝ) (395476266219/500000000000 : ℝ) (51372902361/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0184; no trusted numerical premise.
theorem cover8_leaf0184_exp_radius : (998049970875045957/1000000000000000000 : ℝ) ≤ Real.exp ((-8187/524288 : ℝ)/8) ∧ Real.exp ((-8187/524288 : ℝ)/8) ≤ (499024985437522979/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8187/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0184_exp_lower : (460057118320056751/500000000000000000 : ℝ) ≤ Real.exp ((-5328476568739/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328476568739/8000000000000 : ℝ)/8) ≤ (920114236640113503/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328476568739/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0184_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410983125541/200000000000 : ℝ) ≤ 4*Real.exp (4093/32768 : ℝ)*Real.exp (-mu (radius 8 (8187/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410983125541/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8187/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0184_exp_radius
  have hrNumeric : (984505825939/1000000000000 : ℝ) ≤ Real.exp (-8187/524288 : ℝ) ∧ Real.exp (-8187/524288 : ℝ) ≤ (49225291297/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984505825939/1000000000000 : ℝ) ≤ (radius 8 (8187/65536 : ℝ)) ∧ (radius 8 (8187/65536 : ℝ)) ≤ (49225291297/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8187/65536 : ℝ)) (984505825939/1000000000000 : ℝ) (49225291297/50000000000 : ℝ) (43837967769/250000000000 : ℝ) (175351871083/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8187/65536 : ℝ)) (984505825939/1000000000000 : ℝ) (49225291297/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8187/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984505825939/1000000000000 : ℝ) (49225291297/50000000000 : ℝ) (992252912969/1000000000000 : ℝ) (99225291297/100000000000 : ℝ) (496111334767/500000000000 : ℝ) (31006958423/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8187/65536 : ℝ)) 1 (992252912969/1000000000000 : ℝ) (99225291297/100000000000 : ℝ) (496111334767/500000000000 : ℝ) (31006958423/31250000000 : ℝ) (992237791251/1000000000000 : ℝ) (992237791253/1000000000000 : ℝ) (31007430973/31250000000 : ℝ) (496118895569/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8187/65536 : ℝ)) 2 (992237791251/1000000000000 : ℝ) (992237791253/1000000000000 : ℝ) (31007430973/31250000000 : ℝ) (496118895569/500000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8187/65536 : ℝ)) 3 (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8187/65536 : ℝ)) 4 (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8187/65536 : ℝ)) 5 (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8187/65536 : ℝ)) 6 (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8187/65536 : ℝ)) 7 (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8187/65536 : ℝ))) (43837967769/250000000000 : ℝ) (175351871083/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8187/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43837967769/250000000000 : ℝ) (175351871083/1000000000000 : ℝ) (293837967769/500000000000 : ℝ) (293837967771/500000000000 : ℝ) (6542974507/15625000000 : ℝ) (209375184229/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8187/65536 : ℝ))) 1 (293837967769/500000000000 : ℝ) (293837967771/500000000000 : ℝ) (6542974507/15625000000 : ℝ) (209375184229/500000000000 : ℝ) (503213151993/1000000000000 : ℝ) (15725411/31250000 : ℝ) (248037050929/500000000000 : ℝ) (248037050933/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8187/65536 : ℝ))) 2 (503213151993/1000000000000 : ℝ) (15725411/31250000 : ℝ) (248037050929/500000000000 : ℝ) (248037050933/500000000000 : ℝ) (19985745077/40000000000 : ℝ) (499643626933/1000000000000 : ℝ) (99926175233/200000000000 : ℝ) (249815438087/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8187/65536 : ℝ))) 3 (19985745077/40000000000 : ℝ) (499643626933/1000000000000 : ℝ) (99926175233/200000000000 : ℝ) (249815438087/500000000000 : ℝ) (99927450309/200000000000 : ℝ) (249818625777/500000000000 : ℝ) (31227328219/62500000000 : ℝ) (499637251513/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8187/65536 : ℝ))) 4 (99927450309/200000000000 : ℝ) (249818625777/500000000000 : ℝ) (31227328219/62500000000 : ℝ) (499637251513/1000000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8187/65536 : ℝ))) 5 (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8187/65536 : ℝ))) 6 (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8187/65536 : ℝ))) 7 (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8187/65536 : ℝ)) hmem 8 (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8187/65536 : ℝ))) hcmem 8 (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8187/65536 : ℝ)) (992237791193/1000000000000 : ℝ) (248059447799/250000000000 : ℝ) (124909312881/250000000000 : ℝ) (249818625767/500000000000 : ℝ) (790968018339/1000000000000 : ℝ) (395484009179/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0184_exp_lower
  have heNumeric : (410983125541/200000000000 : ℝ)/4 ≤ Real.exp (-5328476568739/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410983125541/200000000000 : ℝ)/4 ≤ Real.exp ((4093/32768 : ℝ)-(395484009179/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4093/32768 : ℝ) (8187/65536 : ℝ) (395484009179/500000000000 : ℝ) (410983125541/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0185; no trusted numerical premise.
theorem cover8_leaf0185_exp_radius : (199609946584283679/200000000000000000 : ℝ) ≤ Real.exp ((-2047/131072 : ℝ)/8) ∧ Real.exp ((-2047/131072 : ℝ)/8) ≤ (249512433230354599/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2047/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0185_exp_lower : (460057105332475557/500000000000000000 : ℝ) ≤ Real.exp ((-2131391350193/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131391350193/3200000000000 : ℝ)/8) ≤ (184022842132990223/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131391350193/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0185_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64216098863/31250000000 : ℝ) ≤ 4*Real.exp (8187/65536 : ℝ)*Real.exp (-mu (radius 8 (2047/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (64216098863/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2047/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0185_exp_radius
  have hrNumeric : (196900789629/200000000000 : ℝ) ≤ Real.exp (-2047/131072 : ℝ) ∧ Real.exp (-2047/131072 : ℝ) ≤ (492251974073/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196900789629/200000000000 : ℝ) ≤ (radius 8 (2047/16384 : ℝ)) ∧ (radius 8 (2047/16384 : ℝ)) ≤ (492251974073/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2047/16384 : ℝ)) (196900789629/200000000000 : ℝ) (492251974073/500000000000 : ℝ) (87681206773/500000000000 : ℝ) (175362413553/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2047/16384 : ℝ)) (196900789629/200000000000 : ℝ) (492251974073/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2047/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196900789629/200000000000 : ℝ) (492251974073/500000000000 : ℝ) (124031496759/125000000000 : ℝ) (992251974073/1000000000000 : ℝ) (496110861639/500000000000 : ℝ) (992221723279/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2047/16384 : ℝ)) 1 (124031496759/125000000000 : ℝ) (992251974073/1000000000000 : ℝ) (496110861639/500000000000 : ℝ) (992221723279/1000000000000 : ℝ) (39689473947/40000000000 : ℝ) (248059212169/250000000000 : ℝ) (992236848559/1000000000000 : ℝ) (992236848561/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2047/16384 : ℝ)) 2 (39689473947/40000000000 : ℝ) (248059212169/250000000000 : ℝ) (992236848559/1000000000000 : ℝ) (992236848561/1000000000000 : ℝ) (992236848617/1000000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2047/16384 : ℝ)) 3 (992236848617/1000000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2047/16384 : ℝ)) 4 (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2047/16384 : ℝ)) 5 (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2047/16384 : ℝ)) 6 (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2047/16384 : ℝ)) 7 (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2047/16384 : ℝ))) (87681206773/500000000000 : ℝ) (175362413553/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2047/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87681206773/500000000000 : ℝ) (175362413553/1000000000000 : ℝ) (587681206773/1000000000000 : ℝ) (587681206777/1000000000000 : ℝ) (26172684767/62500000000 : ℝ) (418762956281/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2047/16384 : ℝ))) 1 (587681206773/1000000000000 : ℝ) (587681206777/1000000000000 : ℝ) (26172684767/62500000000 : ℝ) (418762956281/1000000000000 : ℝ) (251611040761/500000000000 : ℝ) (503222081529/1000000000000 : ℝ) (31005236421/62500000000 : ℝ) (62010472843/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2047/16384 : ℝ))) 2 (251611040761/500000000000 : ℝ) (503222081529/1000000000000 : ℝ) (31005236421/62500000000 : ℝ) (62010472843/125000000000 : ℝ) (499652932129/1000000000000 : ℝ) (499652932137/1000000000000 : ℝ) (49964018429/100000000000 : ℝ) (249820092149/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2047/16384 : ℝ))) 3 (499652932129/1000000000000 : ℝ) (499652932137/1000000000000 : ℝ) (49964018429/100000000000 : ℝ) (249820092149/500000000000 : ℝ) (499646558209/1000000000000 : ℝ) (249823279109/500000000000 : ℝ) (62455819771/125000000000 : ℝ) (499646558177/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2047/16384 : ℝ))) 4 (499646558209/1000000000000 : ℝ) (249823279109/500000000000 : ℝ) (62455819771/125000000000 : ℝ) (499646558177/1000000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2047/16384 : ℝ))) 5 (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2047/16384 : ℝ))) 6 (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2047/16384 : ℝ))) 7 (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2047/16384 : ℝ)) hmem 8 (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2047/16384 : ℝ))) hcmem 8 (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2047/16384 : ℝ)) (124029606077/125000000000 : ℝ) (992236848619/1000000000000 : ℝ) (124911639547/250000000000 : ℝ) (249823279099/500000000000 : ℝ) (79098350297/100000000000 : ℝ) (79098350299/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0185_exp_lower
  have heNumeric : (64216098863/31250000000 : ℝ)/4 ≤ Real.exp (-2131391350193/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64216098863/31250000000 : ℝ)/4 ≤ Real.exp ((8187/65536 : ℝ)-(79098350299/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8187/65536 : ℝ) (2047/16384 : ℝ) (79098350299/100000000000 : ℝ) (64216098863/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0186; no trusted numerical premise.
theorem cover8_leaf0186_exp_radius : (499024747483923783/500000000000000000 : ℝ) ≤ Real.exp ((-8189/524288 : ℝ)/8) ∧ Real.exp ((-8189/524288 : ℝ)/8) ≤ (998049494967847567/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8189/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0186_exp_lower : (9201141848383879/10000000000000000 : ℝ) ≤ Real.exp ((-532848017189/800000000000 : ℝ)/8) ∧ Real.exp ((-532848017189/800000000000 : ℝ)/8) ≤ (920114184838387901/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532848017189/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0186_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054914702183/1000000000000 : ℝ) ≤ 4*Real.exp (2047/16384 : ℝ)*Real.exp (-mu (radius 8 (8189/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054914702183/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8189/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0186_exp_radius
  have hrNumeric : (196900414071/200000000000 : ℝ) ≤ Real.exp (-8189/524288 : ℝ) ∧ Real.exp (-8189/524288 : ℝ) ≤ (246125517589/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196900414071/200000000000 : ℝ) ≤ (radius 8 (8189/65536 : ℝ)) ∧ (radius 8 (8189/65536 : ℝ)) ≤ (246125517589/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8189/65536 : ℝ)) (196900414071/200000000000 : ℝ) (246125517589/250000000000 : ℝ) (8768647767/50000000000 : ℝ) (87686477673/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8189/65536 : ℝ)) (196900414071/200000000000 : ℝ) (246125517589/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8189/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196900414071/200000000000 : ℝ) (246125517589/250000000000 : ℝ) (992251035177/1000000000000 : ℝ) (496125517589/500000000000 : ℝ) (496110388511/500000000000 : ℝ) (992220777023/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8189/65536 : ℝ)) 1 (992251035177/1000000000000 : ℝ) (496125517589/500000000000 : ℝ) (496110388511/500000000000 : ℝ) (992220777023/1000000000000 : ℝ) (992235906099/1000000000000 : ℝ) (992235906101/1000000000000 : ℝ) (15503686031/15625000000 : ℝ) (496117952993/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8189/65536 : ℝ)) 2 (992235906099/1000000000000 : ℝ) (992235906101/1000000000000 : ℝ) (15503686031/15625000000 : ℝ) (496117952993/500000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8189/65536 : ℝ)) 3 (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8189/65536 : ℝ)) 4 (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8189/65536 : ℝ)) 5 (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8189/65536 : ℝ)) 6 (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8189/65536 : ℝ)) 7 (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8189/65536 : ℝ))) (8768647767/50000000000 : ℝ) (87686477673/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8189/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8768647767/50000000000 : ℝ) (87686477673/500000000000 : ℝ) (58768647767/100000000000 : ℝ) (587686477673/1000000000000 : ℝ) (41877554291/100000000000 : ℝ) (209387771459/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8189/65536 : ℝ))) 1 (58768647767/100000000000 : ℝ) (587686477673/1000000000000 : ℝ) (41877554291/100000000000 : ℝ) (209387771459/500000000000 : ℝ) (50323101029/100000000000 : ℝ) (62903876287/125000000000 : ℝ) (496093462713/1000000000000 : ℝ) (1550292071/3125000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8189/65536 : ℝ))) 2 (50323101029/100000000000 : ℝ) (62903876287/125000000000 : ℝ) (496093462713/1000000000000 : ℝ) (1550292071/3125000000 : ℝ) (499662236501/1000000000000 : ℝ) (124915559127/250000000000 : ℝ) (499649491583/1000000000000 : ℝ) (49964949159/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8189/65536 : ℝ))) 3 (499662236501/1000000000000 : ℝ) (124915559127/250000000000 : ℝ) (499649491583/1000000000000 : ℝ) (49964949159/100000000000 : ℝ) (249827932021/500000000000 : ℝ) (499655864049/1000000000000 : ℝ) (499655864001/1000000000000 : ℝ) (499655864009/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8189/65536 : ℝ))) 4 (249827932021/500000000000 : ℝ) (499655864049/1000000000000 : ℝ) (499655864001/1000000000000 : ℝ) (499655864009/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8189/65536 : ℝ))) 5 (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8189/65536 : ℝ))) 6 (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8189/65536 : ℝ))) 7 (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8189/65536 : ℝ)) hmem 8 (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8189/65536 : ℝ))) hcmem 8 (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8189/65536 : ℝ)) (992235906041/1000000000000 : ℝ) (248058976511/250000000000 : ℝ) (499655864021/1000000000000 : ℝ) (499655864029/1000000000000 : ℝ) (395499493157/500000000000 : ℝ) (79099898633/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0186_exp_lower
  have heNumeric : (2054914702183/1000000000000 : ℝ)/4 ≤ Real.exp (-532848017189/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054914702183/1000000000000 : ℝ)/4 ≤ Real.exp ((2047/16384 : ℝ)-(79099898633/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2047/16384 : ℝ) (8189/65536 : ℝ) (79099898633/100000000000 : ℝ) (2054914702183/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0187; no trusted numerical premise.
theorem cover8_leaf0187_exp_radius : (998049257014333469/1000000000000000000 : ℝ) ≤ Real.exp ((-4095/262144 : ℝ)/8) ∧ Real.exp ((-4095/262144 : ℝ)/8) ≤ (99804925701433347/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4095/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0187_exp_lower : (184022831831693721/200000000000000000 : ℝ) ≤ Real.exp ((-2131392783239/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131392783239/3200000000000 : ℝ)/8) ≤ (460057079579234303/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131392783239/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0187_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205491424337/100000000000 : ℝ) ≤ 4*Real.exp (8189/65536 : ℝ)*Real.exp (-mu (radius 8 (4095/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (205491424337/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4095/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0187_exp_radius
  have hrNumeric : (123062524071/125000000000 : ℝ) ≤ Real.exp (-4095/262144 : ℝ) ∧ Real.exp (-4095/262144 : ℝ) ≤ (984500192569/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123062524071/125000000000 : ℝ) ≤ (radius 8 (4095/32768 : ℝ)) ∧ (radius 8 (4095/32768 : ℝ)) ≤ (984500192569/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4095/32768 : ℝ)) (123062524071/125000000000 : ℝ) (984500192569/1000000000000 : ℝ) (175383496463/1000000000000 : ℝ) (175383496469/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4095/32768 : ℝ)) (123062524071/125000000000 : ℝ) (984500192569/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4095/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123062524071/125000000000 : ℝ) (984500192569/1000000000000 : ℝ) (248062524071/250000000000 : ℝ) (198450019257/200000000000 : ℝ) (992219830767/1000000000000 : ℝ) (62013739423/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4095/32768 : ℝ)) 1 (248062524071/250000000000 : ℝ) (198450019257/200000000000 : ℝ) (992219830767/1000000000000 : ℝ) (62013739423/62500000000 : ℝ) (39689398541/40000000000 : ℝ) (992234963527/1000000000000 : ℝ) (99223496341/100000000000 : ℝ) (248058740853/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4095/32768 : ℝ)) 2 (39689398541/40000000000 : ℝ) (992234963527/1000000000000 : ℝ) (99223496341/100000000000 : ℝ) (248058740853/250000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4095/32768 : ℝ)) 3 (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4095/32768 : ℝ)) 4 (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4095/32768 : ℝ)) 5 (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4095/32768 : ℝ)) 6 (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4095/32768 : ℝ)) 7 (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4095/32768 : ℝ))) (175383496463/1000000000000 : ℝ) (175383496469/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4095/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175383496463/1000000000000 : ℝ) (175383496469/1000000000000 : ℝ) (587691748231/1000000000000 : ℝ) (117538349647/200000000000 : ℝ) (418788128369/1000000000000 : ℝ) (418788128377/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4095/32768 : ℝ))) 1 (587691748231/1000000000000 : ℝ) (117538349647/200000000000 : ℝ) (418788128369/1000000000000 : ℝ) (418788128377/1000000000000 : ℝ) (5032399383/10000000000 : ℝ) (251619969153/500000000000 : ℝ) (99220628359/200000000000 : ℝ) (496103141803/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4095/32768 : ℝ))) 2 (5032399383/10000000000 : ℝ) (251619969153/500000000000 : ℝ) (99220628359/200000000000 : ℝ) (496103141803/1000000000000 : ℝ) (499671540047/1000000000000 : ℝ) (99934308011/200000000000 : ℝ) (15614337439/31250000000 : ℝ) (62457349757/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4095/32768 : ℝ))) 3 (499671540047/1000000000000 : ℝ) (99934308011/200000000000 : ℝ) (15614337439/31250000000 : ℝ) (62457349757/125000000000 : ℝ) (499665169047/1000000000000 : ℝ) (15614536533/31250000000 : ℝ) (249832584503/500000000000 : ℝ) (99933033803/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4095/32768 : ℝ))) 4 (499665169047/1000000000000 : ℝ) (15614536533/31250000000 : ℝ) (249832584503/500000000000 : ℝ) (99933033803/200000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4095/32768 : ℝ))) 5 (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4095/32768 : ℝ))) 6 (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4095/32768 : ℝ))) 7 (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4095/32768 : ℝ)) hmem 8 (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4095/32768 : ℝ))) hcmem 8 (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4095/32768 : ℝ)) (992234963467/1000000000000 : ℝ) (99223496347/100000000000 : ℝ) (249832584513/500000000000 : ℝ) (124916292259/250000000000 : ℝ) (98876808547/125000000000 : ℝ) (158202893679/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0187_exp_lower
  have heNumeric : (205491424337/100000000000 : ℝ)/4 ≤ Real.exp (-2131392783239/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205491424337/100000000000 : ℝ)/4 ≤ Real.exp ((8189/65536 : ℝ)-(158202893679/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8189/65536 : ℝ) (4095/32768 : ℝ) (158202893679/200000000000 : ℝ) (205491424337/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0188; no trusted numerical premise.
theorem cover8_leaf0188_exp_radius : (124756127382609513/125000000000000000 : ℝ) ≤ Real.exp ((-8191/524288 : ℝ)/8) ∧ Real.exp ((-8191/524288 : ℝ)/8) ≤ (199609803812175221/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8191/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0188_exp_lower : (184022826725406689/200000000000000000 : ℝ) ≤ Real.exp ((-5328483733977/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328483733977/8000000000000 : ℝ)/8) ≤ (460057066813516723/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328483733977/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0188_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205491378721/100000000000 : ℝ) ≤ 4*Real.exp (4095/32768 : ℝ)*Real.exp (-mu (radius 8 (8191/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205491378721/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8191/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0188_exp_radius
  have hrNumeric : (196899662957/200000000000 : ℝ) ≤ Real.exp (-8191/524288 : ℝ) ∧ Real.exp (-8191/524288 : ℝ) ≤ (492249157393/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196899662957/200000000000 : ℝ) ≤ (radius 8 (8191/65536 : ℝ)) ∧ (radius 8 (8191/65536 : ℝ)) ≤ (492249157393/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8191/65536 : ℝ)) (196899662957/200000000000 : ℝ) (492249157393/500000000000 : ℝ) (175394036909/1000000000000 : ℝ) (43848509229/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8191/65536 : ℝ)) (196899662957/200000000000 : ℝ) (492249157393/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8191/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196899662957/200000000000 : ℝ) (492249157393/500000000000 : ℝ) (62015572337/62500000000 : ℝ) (992249157393/1000000000000 : ℝ) (992218884513/1000000000000 : ℝ) (496109442257/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8191/65536 : ℝ)) 1 (62015572337/62500000000 : ℝ) (992249157393/1000000000000 : ℝ) (992218884513/1000000000000 : ℝ) (496109442257/500000000000 : ℝ) (124029252619/125000000000 : ℝ) (496117010477/500000000000 : ℝ) (992234020837/1000000000000 : ℝ) (992234020839/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8191/65536 : ℝ)) 2 (124029252619/125000000000 : ℝ) (496117010477/500000000000 : ℝ) (992234020837/1000000000000 : ℝ) (992234020839/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8191/65536 : ℝ)) 3 (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8191/65536 : ℝ)) 4 (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8191/65536 : ℝ)) 5 (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8191/65536 : ℝ)) 6 (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8191/65536 : ℝ)) 7 (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8191/65536 : ℝ))) (175394036909/1000000000000 : ℝ) (43848509229/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8191/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175394036909/1000000000000 : ℝ) (43848509229/250000000000 : ℝ) (293848509227/500000000000 : ℝ) (293848509229/500000000000 : ℝ) (418800712641/1000000000000 : ℝ) (8376014253/20000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8191/65536 : ℝ))) 1 (293848509227/500000000000 : ℝ) (293848509229/500000000000 : ℝ) (418800712641/1000000000000 : ℝ) (8376014253/20000000000 : ℝ) (503248865547/1000000000000 : ℝ) (251624432777/500000000000 : ℝ) (62014102497/125000000000 : ℝ) (99222563997/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8191/65536 : ℝ))) 2 (503248865547/1000000000000 : ℝ) (251624432777/500000000000 : ℝ) (62014102497/125000000000 : ℝ) (99222563997/200000000000 : ℝ) (499680842761/1000000000000 : ℝ) (49968084277/100000000000 : ℝ) (499668103681/1000000000000 : ℝ) (49966810369/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8191/65536 : ℝ))) 3 (499680842761/1000000000000 : ℝ) (49968084277/100000000000 : ℝ) (499668103681/1000000000000 : ℝ) (49966810369/100000000000 : ℝ) (499674473221/1000000000000 : ℝ) (49967447323/100000000000 : ℝ) (24983723659/50000000000 : ℝ) (49967447319/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8191/65536 : ℝ))) 4 (499674473221/1000000000000 : ℝ) (49967447323/100000000000 : ℝ) (24983723659/50000000000 : ℝ) (49967447319/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8191/65536 : ℝ))) 5 (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8191/65536 : ℝ))) 6 (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8191/65536 : ℝ))) 7 (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8191/65536 : ℝ)) hmem 8 (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8191/65536 : ℝ))) hcmem 8 (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8191/65536 : ℝ)) (496117010447/500000000000 : ℝ) (992234020897/1000000000000 : ℝ) (1249186183/2500000000 : ℝ) (49967447321/100000000000 : ℝ) (15820598983/20000000000 : ℝ) (791029949169/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0188_exp_lower
  have heNumeric : (205491378721/100000000000 : ℝ)/4 ≤ Real.exp (-5328483733977/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205491378721/100000000000 : ℝ)/4 ≤ Real.exp ((4095/32768 : ℝ)-(791029949169/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4095/32768 : ℝ) (8191/65536 : ℝ) (791029949169/1000000000000 : ℝ) (205491378721/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0189; no trusted numerical premise.
theorem cover8_leaf0189_exp_radius : (62378048819217217/62500000000000000 : ℝ) ≤ Real.exp ((-1/64 : ℝ)/8) ∧ Real.exp ((-1/64 : ℝ)/8) ≤ (998048781107475473/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1/64 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0189_exp_lower : (460057054121293611/500000000000000000 : ℝ) ≤ Real.exp ((-2131394199853/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131394199853/3200000000000 : ℝ)/8) ≤ (920114108242587223/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131394199853/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0189_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054913333677/1000000000000 : ℝ) ≤ 4*Real.exp (8191/65536 : ℝ)*Real.exp (-mu (radius 8 (1/8 : ℝ))) ∧ (20549/10000 : ℝ) < (2054913333677/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1/8 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0189_exp_radius
  have hrNumeric : (196899287401/200000000000 : ℝ) ≤ Real.exp (-1/64 : ℝ) ∧ Real.exp (-1/64 : ℝ) ≤ (492248218503/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196899287401/200000000000 : ℝ) ≤ (radius 8 (1/8 : ℝ)) ∧ (radius 8 (1/8 : ℝ)) ≤ (492248218503/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1/8 : ℝ)) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ) (87702288343/500000000000 : ℝ) (43851144173/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1/8 : ℝ)) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1/8 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196899287401/200000000000 : ℝ) (492248218503/500000000000 : ℝ) (496124109251/500000000000 : ℝ) (992248218503/1000000000000 : ℝ) (49610896913/50000000000 : ℝ) (992217938261/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1/8 : ℝ)) 1 (496124109251/500000000000 : ℝ) (992248218503/1000000000000 : ℝ) (49610896913/50000000000 : ℝ) (992217938261/1000000000000 : ℝ) (992233078381/1000000000000 : ℝ) (496116539191/500000000000 : ℝ) (198446615653/200000000000 : ℝ) (992233078267/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1/8 : ℝ)) 2 (992233078381/1000000000000 : ℝ) (496116539191/500000000000 : ℝ) (198446615653/200000000000 : ℝ) (992233078267/1000000000000 : ℝ) (992233078323/1000000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1/8 : ℝ)) 3 (992233078323/1000000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1/8 : ℝ)) 4 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1/8 : ℝ)) 5 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1/8 : ℝ)) 6 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1/8 : ℝ)) 7 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1/8 : ℝ))) (87702288343/500000000000 : ℝ) (43851144173/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1/8 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87702288343/500000000000 : ℝ) (43851144173/250000000000 : ℝ) (587702288343/1000000000000 : ℝ) (293851144173/500000000000 : ℝ) (52351661967/125000000000 : ℝ) (83762659149/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1/8 : ℝ))) 1 (587702288343/1000000000000 : ℝ) (293851144173/500000000000 : ℝ) (52351661967/125000000000 : ℝ) (83762659149/200000000000 : ℝ) (503257792039/1000000000000 : ℝ) (251628896023/500000000000 : ℝ) (99224499453/200000000000 : ℝ) (62015312159/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1/8 : ℝ))) 2 (503257792039/1000000000000 : ℝ) (251628896023/500000000000 : ℝ) (99224499453/200000000000 : ℝ) (62015312159/125000000000 : ℝ) (124922536163/250000000000 : ℝ) (499690144659/1000000000000 : ℝ) (499677408489/1000000000000 : ℝ) (499677408497/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1/8 : ℝ))) 3 (124922536163/250000000000 : ℝ) (499690144659/1000000000000 : ℝ) (499677408489/1000000000000 : ℝ) (499677408497/1000000000000 : ℝ) (49968377657/100000000000 : ℝ) (249841888289/500000000000 : ℝ) (499683776529/1000000000000 : ℝ) (249841888269/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1/8 : ℝ))) 4 (49968377657/100000000000 : ℝ) (249841888289/500000000000 : ℝ) (499683776529/1000000000000 : ℝ) (249841888269/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1/8 : ℝ))) 5 (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1/8 : ℝ))) 6 (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1/8 : ℝ))) 7 (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1/8 : ℝ)) hmem 8 (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1/8 : ℝ))) hcmem 8 (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1/8 : ℝ)) (496116539161/500000000000 : ℝ) (39689323133/40000000000 : ℝ) (499683776549/1000000000000 : ℝ) (249841888279/500000000000 : ℝ) (791045428647/1000000000000 : ℝ) (158209085733/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0189_exp_lower
  have heNumeric : (2054913333677/1000000000000 : ℝ)/4 ≤ Real.exp (-2131394199853/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054913333677/1000000000000 : ℝ)/4 ≤ Real.exp ((8191/65536 : ℝ)-(158209085733/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8191/65536 : ℝ) (1/8 : ℝ) (158209085733/200000000000 : ℝ) (2054913333677/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0190; no trusted numerical premise.
theorem cover8_leaf0190_exp_radius : (998048543154131573/1000000000000000000 : ℝ) ≤ Real.exp ((-8193/524288 : ℝ)/8) ∧ Real.exp ((-8193/524288 : ℝ)/8) ≤ (499024271577065787/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8193/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0190_exp_lower : (460057041503025019/500000000000000000 : ℝ) ≤ Real.exp ((-1065697451/1600000000 : ℝ)/8) ∧ Real.exp ((-1065697451/1600000000 : ℝ)/8) ≤ (920114083006050039/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065697451/1600000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0190_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027456441393/500000000000 : ℝ) ≤ 4*Real.exp (1/8 : ℝ)*Real.exp (-mu (radius 8 (8193/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027456441393/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8193/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0190_exp_radius
  have hrNumeric : (984494559229/1000000000000 : ℝ) ≤ Real.exp (-8193/524288 : ℝ) ∧ Real.exp (-8193/524288 : ℝ) ≤ (98449455923/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984494559229/1000000000000 : ℝ) ≤ (radius 8 (8193/65536 : ℝ)) ∧ (radius 8 (8193/65536 : ℝ)) ≤ (98449455923/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8193/65536 : ℝ)) (984494559229/1000000000000 : ℝ) (98449455923/100000000000 : ℝ) (87707557893/500000000000 : ℝ) (175415115793/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8193/65536 : ℝ)) (984494559229/1000000000000 : ℝ) (98449455923/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8193/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984494559229/1000000000000 : ℝ) (98449455923/100000000000 : ℝ) (496123639807/500000000000 : ℝ) (198449455923/200000000000 : ℝ) (992216992007/1000000000000 : ℝ) (992216992009/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8193/65536 : ℝ)) 1 (496123639807/500000000000 : ℝ) (198449455923/200000000000 : ℝ) (992216992007/1000000000000 : ℝ) (992216992009/1000000000000 : ℝ) (99223213581/100000000000 : ℝ) (248058033953/250000000000 : ℝ) (496116067847/500000000000 : ℝ) (992232135697/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8193/65536 : ℝ)) 2 (99223213581/100000000000 : ℝ) (248058033953/250000000000 : ℝ) (496116067847/500000000000 : ℝ) (992232135697/1000000000000 : ℝ) (124029016969/125000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8193/65536 : ℝ)) 3 (124029016969/125000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8193/65536 : ℝ)) 4 (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8193/65536 : ℝ)) 5 (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8193/65536 : ℝ)) 6 (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8193/65536 : ℝ)) 7 (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8193/65536 : ℝ))) (87707557893/500000000000 : ℝ) (175415115793/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8193/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87707557893/500000000000 : ℝ) (175415115793/1000000000000 : ℝ) (587707557893/1000000000000 : ℝ) (587707557897/1000000000000 : ℝ) (209412938823/500000000000 : ℝ) (83765175531/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8193/65536 : ℝ))) 1 (587707557893/1000000000000 : ℝ) (587707557897/1000000000000 : ℝ) (209412938823/500000000000 : ℝ) (83765175531/200000000000 : ℝ) (503266717769/1000000000000 : ℝ) (31454169861/62500000000 : ℝ) (496132173653/1000000000000 : ℝ) (496132173661/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8193/65536 : ℝ))) 2 (503266717769/1000000000000 : ℝ) (31454169861/62500000000 : ℝ) (496132173653/1000000000000 : ℝ) (496132173661/1000000000000 : ℝ) (499699445711/1000000000000 : ℝ) (499699445719/1000000000000 : ℝ) (31230419529/62500000000 : ℝ) (499686712473/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8193/65536 : ℝ))) 3 (499699445711/1000000000000 : ℝ) (499699445719/1000000000000 : ℝ) (31230419529/62500000000 : ℝ) (499686712473/1000000000000 : ℝ) (499693079087/1000000000000 : ℝ) (62461634887/125000000000 : ℝ) (249846539523/500000000000 : ℝ) (31230817441/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8193/65536 : ℝ))) 4 (499693079087/1000000000000 : ℝ) (62461634887/125000000000 : ℝ) (249846539523/500000000000 : ℝ) (31230817441/62500000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8193/65536 : ℝ))) 5 (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8193/65536 : ℝ))) 6 (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8193/65536 : ℝ))) 7 (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8193/65536 : ℝ)) hmem 8 (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8193/65536 : ℝ))) hcmem 8 (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8193/65536 : ℝ)) (992232135751/1000000000000 : ℝ) (198446427151/200000000000 : ℝ) (249846539533/500000000000 : ℝ) (124923269769/250000000000 : ℝ) (158212181371/200000000000 : ℝ) (1265697451/1600000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0190_exp_lower
  have heNumeric : (1027456441393/500000000000 : ℝ)/4 ≤ Real.exp (-1065697451/1600000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027456441393/500000000000 : ℝ)/4 ≤ Real.exp ((1/8 : ℝ)-(1265697451/1600000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1/8 : ℝ) (8193/65536 : ℝ) (1265697451/1600000000 : ℝ) (1027456441393/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0191; no trusted numerical premise.
theorem cover8_leaf0191_exp_radius : (499024152600422203/500000000000000000 : ℝ) ≤ Real.exp ((-4097/262144 : ℝ)/8) ∧ Real.exp ((-4097/262144 : ℝ)/8) ≤ (998048305200844407/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4097/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0191_exp_lower : (230028514479182949/250000000000000000 : ℝ) ≤ Real.exp ((-2131395600051/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131395600051/3200000000000 : ℝ)/8) ≤ (920114057916731797/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131395600051/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0191_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196497381/40000000000 : ℝ) ≤ 4*Real.exp (8193/65536 : ℝ)*Real.exp (-mu (radius 8 (4097/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (82196497381/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4097/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0191_exp_radius
  have hrNumeric : (61530792591/62500000000 : ℝ) ≤ Real.exp (-4097/262144 : ℝ) ∧ Real.exp (-4097/262144 : ℝ) ≤ (984492681457/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61530792591/62500000000 : ℝ) ≤ (radius 8 (4097/32768 : ℝ)) ∧ (radius 8 (4097/32768 : ℝ)) ≤ (984492681457/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4097/32768 : ℝ)) (61530792591/62500000000 : ℝ) (984492681457/1000000000000 : ℝ) (175425654217/1000000000000 : ℝ) (10964103389/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4097/32768 : ℝ)) (61530792591/62500000000 : ℝ) (984492681457/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4097/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61530792591/62500000000 : ℝ) (984492681457/1000000000000 : ℝ) (124030792591/125000000000 : ℝ) (992246340729/1000000000000 : ℝ) (248054011439/250000000000 : ℝ) (992216045757/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4097/32768 : ℝ)) 1 (124030792591/125000000000 : ℝ) (992246340729/1000000000000 : ℝ) (248054011439/250000000000 : ℝ) (992216045757/1000000000000 : ℝ) (496115596621/500000000000 : ℝ) (992231193243/1000000000000 : ℝ) (496115596563/500000000000 : ℝ) (124028899141/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4097/32768 : ℝ)) 2 (496115596621/500000000000 : ℝ) (992231193243/1000000000000 : ℝ) (496115596563/500000000000 : ℝ) (124028899141/125000000000 : ℝ) (31007224787/31250000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4097/32768 : ℝ)) 3 (31007224787/31250000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4097/32768 : ℝ)) 4 (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4097/32768 : ℝ)) 5 (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4097/32768 : ℝ)) 6 (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4097/32768 : ℝ)) 7 (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4097/32768 : ℝ))) (175425654217/1000000000000 : ℝ) (10964103389/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4097/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175425654217/1000000000000 : ℝ) (10964103389/62500000000 : ℝ) (146928206777/250000000000 : ℝ) (73464103389/125000000000 : ℝ) (209419229189/500000000000 : ℝ) (104709614597/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4097/32768 : ℝ))) 1 (146928206777/250000000000 : ℝ) (73464103389/125000000000 : ℝ) (209419229189/500000000000 : ℝ) (104709614597/250000000000 : ℝ) (503275642743/1000000000000 : ℝ) (2013102571/4000000000 : ℝ) (248070924573/500000000000 : ℝ) (99228369831/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4097/32768 : ℝ))) 2 (503275642743/1000000000000 : ℝ) (2013102571/4000000000 : ℝ) (248070924573/500000000000 : ℝ) (99228369831/200000000000 : ℝ) (62463593243/125000000000 : ℝ) (499708745953/1000000000000 : ℝ) (249848007807/500000000000 : ℝ) (499696015623/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4097/32768 : ℝ))) 3 (62463593243/125000000000 : ℝ) (499708745953/1000000000000 : ℝ) (249848007807/500000000000 : ℝ) (499696015623/1000000000000 : ℝ) (499702380779/1000000000000 : ℝ) (124925595197/250000000000 : ℝ) (249851190369/500000000000 : ℝ) (124925595187/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4097/32768 : ℝ))) 4 (499702380779/1000000000000 : ℝ) (124925595197/250000000000 : ℝ) (249851190369/500000000000 : ℝ) (124925595187/250000000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4097/32768 : ℝ))) 5 (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4097/32768 : ℝ))) 6 (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4097/32768 : ℝ))) 7 (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4097/32768 : ℝ)) hmem 8 (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4097/32768 : ℝ))) hcmem 8 (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4097/32768 : ℝ)) (992231193183/1000000000000 : ℝ) (496115596593/500000000000 : ℝ) (249851190379/500000000000 : ℝ) (15615699399/31250000000 : ℝ) (395538191893/500000000000 : ℝ) (158215276761/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0191_exp_lower
  have heNumeric : (82196497381/40000000000 : ℝ)/4 ≤ Real.exp (-2131395600051/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196497381/40000000000 : ℝ)/4 ≤ Real.exp ((8193/65536 : ℝ)-(158215276761/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8193/65536 : ℝ) (4097/32768 : ℝ) (158215276761/200000000000 : ℝ) (82196497381/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0192; no trusted numerical premise.
theorem cover8_leaf0192_exp_radius : (998048067247613971/1000000000000000000 : ℝ) ≤ Real.exp ((-8195/524288 : ℝ)/8) ∧ Real.exp ((-8195/524288 : ℝ)/8) ≤ (249512016811903493/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8195/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0192_exp_lower : (920114032975437583/1000000000000000000 : ℝ) ≤ Real.exp ((-5328490734959/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328490734959/8000000000000 : ℝ)/8) ≤ (57507127060964849/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328490734959/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0192_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054911988909/1000000000000 : ℝ) ≤ 4*Real.exp (4097/32768 : ℝ)*Real.exp (-mu (radius 8 (8195/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054911988909/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8195/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0192_exp_radius
  have hrNumeric : (984490803687/1000000000000 : ℝ) ≤ Real.exp (-8195/524288 : ℝ) ∧ Real.exp (-8195/524288 : ℝ) ≤ (123061350461/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984490803687/1000000000000 : ℝ) ≤ (radius 8 (8195/65536 : ℝ)) ∧ (radius 8 (8195/65536 : ℝ)) ≤ (123061350461/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8195/65536 : ℝ)) (984490803687/1000000000000 : ℝ) (123061350461/125000000000 : ℝ) (43859047993/250000000000 : ℝ) (87718095989/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8195/65536 : ℝ)) (984490803687/1000000000000 : ℝ) (123061350461/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8195/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984490803687/1000000000000 : ℝ) (123061350461/125000000000 : ℝ) (992245401843/1000000000000 : ℝ) (248061350461/250000000000 : ℝ) (198443019901/200000000000 : ℝ) (992215099507/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8195/65536 : ℝ)) 1 (992245401843/1000000000000 : ℝ) (248061350461/250000000000 : ℝ) (198443019901/200000000000 : ℝ) (992215099507/1000000000000 : ℝ) (496115125337/500000000000 : ℝ) (248057562669/250000000000 : ℝ) (496115125279/500000000000 : ℝ) (3100719533/3125000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8195/65536 : ℝ)) 2 (496115125337/500000000000 : ℝ) (248057562669/250000000000 : ℝ) (496115125279/500000000000 : ℝ) (3100719533/3125000000 : ℝ) (124028781327/125000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8195/65536 : ℝ)) 3 (124028781327/125000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8195/65536 : ℝ)) 4 (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8195/65536 : ℝ)) 5 (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8195/65536 : ℝ)) 6 (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8195/65536 : ℝ)) 7 (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8195/65536 : ℝ))) (43859047993/250000000000 : ℝ) (87718095989/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8195/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43859047993/250000000000 : ℝ) (87718095989/500000000000 : ℝ) (293859047993/500000000000 : ℝ) (587718095989/1000000000000 : ℝ) (209425518963/500000000000 : ℝ) (209425518967/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8195/65536 : ℝ))) 1 (293859047993/500000000000 : ℝ) (587718095989/1000000000000 : ℝ) (209425518963/500000000000 : ℝ) (209425518967/500000000000 : ℝ) (125821141739/250000000000 : ℝ) (251642283481/500000000000 : ℝ) (248075761871/500000000000 : ℝ) (496151523749/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8195/65536 : ℝ))) 2 (125821141739/250000000000 : ℝ) (251642283481/500000000000 : ℝ) (248075761871/500000000000 : ℝ) (496151523749/1000000000000 : ℝ) (499718045349/1000000000000 : ℝ) (124929511339/250000000000 : ℝ) (499705317933/1000000000000 : ℝ) (499705317941/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8195/65536 : ℝ))) 3 (499718045349/1000000000000 : ℝ) (124929511339/250000000000 : ℝ) (499705317933/1000000000000 : ℝ) (499705317941/1000000000000 : ℝ) (499711681641/1000000000000 : ℝ) (499711681649/1000000000000 : ℝ) (312319801/625000000 : ℝ) (62463960201/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8195/65536 : ℝ))) 4 (499711681641/1000000000000 : ℝ) (499711681649/1000000000000 : ℝ) (312319801/625000000 : ℝ) (62463960201/125000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8195/65536 : ℝ))) 5 (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8195/65536 : ℝ))) 6 (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8195/65536 : ℝ))) 7 (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8195/65536 : ℝ)) hmem 8 (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8195/65536 : ℝ))) hcmem 8 (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8195/65536 : ℝ)) (198446050123/200000000000 : ℝ) (496115125309/500000000000 : ℝ) (24985584081/50000000000 : ℝ) (499711681629/1000000000000 : ℝ) (791091859431/1000000000000 : ℝ) (98886482431/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0192_exp_lower
  have heNumeric : (2054911988909/1000000000000 : ℝ)/4 ≤ Real.exp (-5328490734959/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054911988909/1000000000000 : ℝ)/4 ≤ Real.exp ((4097/32768 : ℝ)-(98886482431/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4097/32768 : ℝ) (8195/65536 : ℝ) (98886482431/125000000000 : ℝ) (2054911988909/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0193; no trusted numerical premise.
theorem cover8_leaf0193_exp_radius : (998047829294440269/1000000000000000000 : ℝ) ≤ Real.exp ((-2049/131072 : ℝ)/8) ∧ Real.exp ((-2049/131072 : ℝ)/8) ≤ (99804782929444027/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2049/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0193_exp_lower : (920114008181937359/1000000000000000000 : ℝ) ≤ Real.exp ((-10656984919021/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656984919021/16000000000000 : ℝ)/8) ≤ (11501425102274217/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656984919021/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0193_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455772967/500000000000 : ℝ) ≤ 4*Real.exp (8195/65536 : ℝ)*Real.exp (-mu (radius 8 (2049/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455772967/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2049/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0193_exp_radius
  have hrNumeric : (492244462961/500000000000 : ℝ) ≤ Real.exp (-2049/131072 : ℝ) ∧ Real.exp (-2049/131072 : ℝ) ≤ (984488925923/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492244462961/500000000000 : ℝ) ≤ (radius 8 (2049/16384 : ℝ)) ∧ (radius 8 (2049/16384 : ℝ)) ≤ (984488925923/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2049/16384 : ℝ)) (492244462961/500000000000 : ℝ) (984488925923/1000000000000 : ℝ) (175446729051/1000000000000 : ℝ) (87723364529/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2049/16384 : ℝ)) (492244462961/500000000000 : ℝ) (984488925923/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2049/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492244462961/500000000000 : ℝ) (984488925923/1000000000000 : ℝ) (992244462961/1000000000000 : ℝ) (496122231481/500000000000 : ℝ) (124026769157/125000000000 : ℝ) (992214153257/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2049/16384 : ℝ)) 1 (992244462961/1000000000000 : ℝ) (496122231481/500000000000 : ℝ) (124026769157/125000000000 : ℝ) (992214153257/1000000000000 : ℝ) (248057327027/250000000000 : ℝ) (99222930811/100000000000 : ℝ) (124028663499/125000000000 : ℝ) (496114653997/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2049/16384 : ℝ)) 2 (248057327027/250000000000 : ℝ) (99222930811/100000000000 : ℝ) (124028663499/125000000000 : ℝ) (496114653997/500000000000 : ℝ) (19844586161/20000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2049/16384 : ℝ)) 3 (19844586161/20000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2049/16384 : ℝ)) 4 (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2049/16384 : ℝ)) 5 (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2049/16384 : ℝ)) 6 (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2049/16384 : ℝ)) 7 (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2049/16384 : ℝ))) (175446729051/1000000000000 : ℝ) (87723364529/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2049/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175446729051/1000000000000 : ℝ) (87723364529/500000000000 : ℝ) (23508934581/40000000000 : ℝ) (587723364529/1000000000000 : ℝ) (418863616289/1000000000000 : ℝ) (209431808149/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2049/16384 : ℝ))) 1 (23508934581/40000000000 : ℝ) (587723364529/1000000000000 : ℝ) (418863616289/1000000000000 : ℝ) (209431808149/500000000000 : ℝ) (503293490407/1000000000000 : ℝ) (251646745207/500000000000 : ℝ) (496161197437/1000000000000 : ℝ) (99232239489/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2049/16384 : ℝ))) 2 (503293490407/1000000000000 : ℝ) (251646745207/500000000000 : ℝ) (496161197437/1000000000000 : ℝ) (99232239489/200000000000 : ℝ) (249863671961/500000000000 : ℝ) (49972734393/100000000000 : ℝ) (24985730971/50000000000 : ℝ) (499714619429/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2049/16384 : ℝ))) 3 (249863671961/500000000000 : ℝ) (49972734393/100000000000 : ℝ) (24985730971/50000000000 : ℝ) (499714619429/1000000000000 : ℝ) (499720981671/1000000000000 : ℝ) (6246512271/12500000000 : ℝ) (49972098163/100000000000 : ℝ) (499720981639/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2049/16384 : ℝ))) 4 (499720981671/1000000000000 : ℝ) (6246512271/12500000000 : ℝ) (49972098163/100000000000 : ℝ) (499720981639/1000000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2049/16384 : ℝ))) 5 (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2049/16384 : ℝ))) 6 (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2049/16384 : ℝ))) 7 (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2049/16384 : ℝ)) hmem 8 (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2049/16384 : ℝ))) hcmem 8 (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2049/16384 : ℝ)) (992229308049/1000000000000 : ℝ) (248057327013/250000000000 : ℝ) (9994419633/20000000000 : ℝ) (24986049083/50000000000 : ℝ) (395553666893/500000000000 : ℝ) (395553666903/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0193_exp_lower
  have heNumeric : (1027455772967/500000000000 : ℝ)/4 ≤ Real.exp (-10656984919021/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455772967/500000000000 : ℝ)/4 ≤ Real.exp ((8195/65536 : ℝ)-(395553666903/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8195/65536 : ℝ) (2049/16384 : ℝ) (395553666903/500000000000 : ℝ) (1027455772967/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0194; no trusted numerical premise.
theorem cover8_leaf0194_exp_radius : (9980475913413233/10000000000000000 : ℝ) ≤ Real.exp ((-8197/524288 : ℝ)/8) ∧ Real.exp ((-8197/524288 : ℝ)/8) ≤ (998047591341323301/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8197/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0194_exp_lower : (23002849588391401/25000000000000000 : ℝ) ≤ Real.exp ((-2664247086911/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664247086911/4000000000000 : ℝ)/8) ≤ (920113983535656041/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664247086911/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0194_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205491110559/100000000000 : ℝ) ≤ 4*Real.exp (2049/16384 : ℝ)*Real.exp (-mu (radius 8 (8197/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205491110559/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8197/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0194_exp_radius
  have hrNumeric : (6153044051/6250000000 : ℝ) ≤ Real.exp (-8197/524288 : ℝ) ∧ Real.exp (-8197/524288 : ℝ) ≤ (984487048161/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (6153044051/6250000000 : ℝ) ≤ (radius 8 (8197/65536 : ℝ)) ∧ (radius 8 (8197/65536 : ℝ)) ≤ (984487048161/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8197/65536 : ℝ)) (6153044051/6250000000 : ℝ) (984487048161/1000000000000 : ℝ) (175457265461/1000000000000 : ℝ) (43864316367/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8197/65536 : ℝ)) (6153044051/6250000000 : ℝ) (984487048161/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8197/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (6153044051/6250000000 : ℝ) (984487048161/1000000000000 : ℝ) (12403044051/12500000000 : ℝ) (992243524081/1000000000000 : ℝ) (992213207007/1000000000000 : ℝ) (31006662719/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8197/65536 : ℝ)) 1 (12403044051/12500000000 : ℝ) (992243524081/1000000000000 : ℝ) (992213207007/1000000000000 : ℝ) (31006662719/31250000000 : ℝ) (992228365543/1000000000000 : ℝ) (198445673109/200000000000 : ℝ) (992228365427/1000000000000 : ℝ) (992228365429/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8197/65536 : ℝ)) 2 (992228365543/1000000000000 : ℝ) (198445673109/200000000000 : ℝ) (992228365427/1000000000000 : ℝ) (992228365429/1000000000000 : ℝ) (198445673097/200000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8197/65536 : ℝ)) 3 (198445673097/200000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8197/65536 : ℝ)) 4 (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8197/65536 : ℝ)) 5 (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8197/65536 : ℝ)) 6 (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8197/65536 : ℝ)) 7 (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8197/65536 : ℝ))) (175457265461/1000000000000 : ℝ) (43864316367/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8197/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175457265461/1000000000000 : ℝ) (43864316367/250000000000 : ℝ) (58772863273/100000000000 : ℝ) (293864316367/500000000000 : ℝ) (104719048369/250000000000 : ℝ) (83775238697/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8197/65536 : ℝ))) 1 (58772863273/100000000000 : ℝ) (293864316367/500000000000 : ℝ) (104719048369/250000000000 : ℝ) (83775238697/200000000000 : ℝ) (503302413103/1000000000000 : ℝ) (50330241311/100000000000 : ℝ) (3101067939/6250000000 : ℝ) (62021358781/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8197/65536 : ℝ))) 2 (503302413103/1000000000000 : ℝ) (50330241311/100000000000 : ℝ) (3101067939/6250000000 : ℝ) (62021358781/125000000000 : ℝ) (499736641671/1000000000000 : ℝ) (499736641679/1000000000000 : ℝ) (499723920083/1000000000000 : ℝ) (499723920091/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8197/65536 : ℝ))) 3 (499736641671/1000000000000 : ℝ) (499736641679/1000000000000 : ℝ) (499723920083/1000000000000 : ℝ) (499723920091/1000000000000 : ℝ) (499730280877/1000000000000 : ℝ) (99946056177/200000000000 : ℝ) (124932570209/250000000000 : ℝ) (99946056169/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8197/65536 : ℝ))) 4 (499730280877/1000000000000 : ℝ) (99946056177/200000000000 : ℝ) (124932570209/250000000000 : ℝ) (99946056169/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8197/65536 : ℝ))) 5 (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8197/65536 : ℝ))) 6 (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8197/65536 : ℝ))) 7 (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8197/65536 : ℝ)) hmem 8 (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8197/65536 : ℝ))) hcmem 8 (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8197/65536 : ℝ)) (248057091371/250000000000 : ℝ) (992228365487/1000000000000 : ℝ) (62466285107/125000000000 : ℝ) (99946056173/200000000000 : ℝ) (395561403433/500000000000 : ℝ) (197780701721/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0194_exp_lower
  have heNumeric : (205491110559/100000000000 : ℝ)/4 ≤ Real.exp (-2664247086911/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205491110559/100000000000 : ℝ)/4 ≤ Real.exp ((2049/16384 : ℝ)-(197780701721/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2049/16384 : ℝ) (8197/65536 : ℝ) (197780701721/250000000000 : ℝ) (205491110559/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0195; no trusted numerical premise.
theorem cover8_leaf0195_exp_radius : (998047353388263063/1000000000000000000 : ℝ) ≤ Real.exp ((-4099/262144 : ℝ)/8) ∧ Real.exp ((-4099/262144 : ℝ)/8) ≤ (124755919173532883/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4099/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0195_exp_lower : (9201139590372837/10000000000000000 : ℝ) ≤ Real.exp ((-10656991755691/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656991755691/16000000000000 : ℝ)/8) ≤ (920113959037283701/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656991755691/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0195_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054910667887/1000000000000 : ℝ) ≤ 4*Real.exp (8197/65536 : ℝ)*Real.exp (-mu (radius 8 (4099/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054910667887/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4099/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0195_exp_radius
  have hrNumeric : (492242585201/500000000000 : ℝ) ≤ Real.exp (-4099/262144 : ℝ) ∧ Real.exp (-4099/262144 : ℝ) ≤ (984485170403/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492242585201/500000000000 : ℝ) ≤ (radius 8 (4099/32768 : ℝ)) ∧ (radius 8 (4099/32768 : ℝ)) ≤ (984485170403/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4099/32768 : ℝ)) (492242585201/500000000000 : ℝ) (984485170403/1000000000000 : ℝ) (43866950299/250000000000 : ℝ) (87733900601/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4099/32768 : ℝ)) (492242585201/500000000000 : ℝ) (984485170403/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4099/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492242585201/500000000000 : ℝ) (984485170403/1000000000000 : ℝ) (992242585201/1000000000000 : ℝ) (496121292601/500000000000 : ℝ) (992212260759/1000000000000 : ℝ) (992212260761/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4099/32768 : ℝ)) 1 (992242585201/1000000000000 : ℝ) (496121292601/500000000000 : ℝ) (992212260759/1000000000000 : ℝ) (992212260761/1000000000000 : ℝ) (49611371149/50000000000 : ℝ) (496113711491/500000000000 : ℝ) (62014213929/62500000000 : ℝ) (496113711433/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4099/32768 : ℝ)) 2 (49611371149/50000000000 : ℝ) (496113711491/500000000000 : ℝ) (62014213929/62500000000 : ℝ) (496113711433/500000000000 : ℝ) (496113711461/500000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4099/32768 : ℝ)) 3 (496113711461/500000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4099/32768 : ℝ)) 4 (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4099/32768 : ℝ)) 5 (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4099/32768 : ℝ)) 6 (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4099/32768 : ℝ)) 7 (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4099/32768 : ℝ))) (43866950299/250000000000 : ℝ) (87733900601/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4099/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43866950299/250000000000 : ℝ) (87733900601/500000000000 : ℝ) (293866950299/500000000000 : ℝ) (587733900601/1000000000000 : ℝ) (418888769479/1000000000000 : ℝ) (418888769487/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4099/32768 : ℝ))) 1 (293866950299/500000000000 : ℝ) (587733900601/1000000000000 : ℝ) (418888769479/1000000000000 : ℝ) (418888769487/1000000000000 : ℝ) (251655667519/500000000000 : ℝ) (125827833761/250000000000 : ℝ) (7752820971/15625000000 : ℝ) (496180542151/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4099/32768 : ℝ))) 2 (251655667519/500000000000 : ℝ) (125827833761/250000000000 : ℝ) (7752820971/15625000000 : ℝ) (496180542151/1000000000000 : ℝ) (499745938591/1000000000000 : ℝ) (249872969299/500000000000 : ℝ) (249866609957/500000000000 : ℝ) (249866609961/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4099/32768 : ℝ))) 3 (499745938591/1000000000000 : ℝ) (249872969299/500000000000 : ℝ) (249866609957/500000000000 : ℝ) (249866609961/500000000000 : ℝ) (124934894813/250000000000 : ℝ) (24986978963/50000000000 : ℝ) (124934894803/250000000000 : ℝ) (24986978961/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4099/32768 : ℝ))) 4 (124934894813/250000000000 : ℝ) (24986978963/50000000000 : ℝ) (124934894803/250000000000 : ℝ) (24986978961/50000000000 : ℝ) (15616861851/31250000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4099/32768 : ℝ))) 5 (15616861851/31250000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4099/32768 : ℝ))) 6 (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4099/32768 : ℝ))) 7 (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4099/32768 : ℝ)) hmem 8 (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4099/32768 : ℝ))) hcmem 8 (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4099/32768 : ℝ)) (992227422921/1000000000000 : ℝ) (248056855731/250000000000 : ℝ) (499739579231/1000000000000 : ℝ) (12493489481/25000000000 : ℝ) (395569139329/500000000000 : ℝ) (197784569669/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0195_exp_lower
  have heNumeric : (2054910667887/1000000000000 : ℝ)/4 ≤ Real.exp (-10656991755691/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054910667887/1000000000000 : ℝ)/4 ≤ Real.exp ((8197/65536 : ℝ)-(197784569669/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8197/65536 : ℝ) (4099/32768 : ℝ) (197784569669/250000000000 : ℝ) (2054910667887/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0196; no trusted numerical premise.
theorem cover8_leaf0196_exp_radius : (499023557717629779/500000000000000000 : ℝ) ≤ Real.exp ((-8199/524288 : ℝ)/8) ∧ Real.exp ((-8199/524288 : ℝ)/8) ≤ (998047115435259559/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8199/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0196_exp_lower : (920113934685555171/1000000000000000000 : ℝ) ≤ Real.exp ((-5328497571669/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328497571669/8000000000000 : ℝ)/8) ≤ (230028483671388793/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328497571669/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0196_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455116403/500000000000 : ℝ) ≤ 4*Real.exp (4099/32768 : ℝ)*Real.exp (-mu (radius 8 (8199/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455116403/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8199/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0196_exp_radius
  have hrNumeric : (984483292647/1000000000000 : ℝ) ≤ Real.exp (-8199/524288 : ℝ) ∧ Real.exp (-8199/524288 : ℝ) ≤ (123060411581/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984483292647/1000000000000 : ℝ) ≤ (radius 8 (8199/65536 : ℝ)) ∧ (radius 8 (8199/65536 : ℝ)) ≤ (123060411581/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8199/65536 : ℝ)) (984483292647/1000000000000 : ℝ) (123060411581/125000000000 : ℝ) (175478336261/1000000000000 : ℝ) (175478336267/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8199/65536 : ℝ)) (984483292647/1000000000000 : ℝ) (123060411581/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8199/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984483292647/1000000000000 : ℝ) (123060411581/125000000000 : ℝ) (992241646323/1000000000000 : ℝ) (248060411581/250000000000 : ℝ) (62013207157/62500000000 : ℝ) (496105657257/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8199/65536 : ℝ)) 1 (992241646323/1000000000000 : ℝ) (248060411581/250000000000 : ℝ) (62013207157/62500000000 : ℝ) (496105657257/500000000000 : ℝ) (992226480417/1000000000000 : ℝ) (992226480419/1000000000000 : ℝ) (992226480301/1000000000000 : ℝ) (62014155019/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8199/65536 : ℝ)) 2 (992226480417/1000000000000 : ℝ) (992226480419/1000000000000 : ℝ) (992226480301/1000000000000 : ℝ) (62014155019/62500000000 : ℝ) (992226480359/1000000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8199/65536 : ℝ)) 3 (992226480359/1000000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8199/65536 : ℝ)) 4 (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8199/65536 : ℝ)) 5 (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8199/65536 : ℝ)) 6 (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8199/65536 : ℝ)) 7 (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8199/65536 : ℝ))) (175478336261/1000000000000 : ℝ) (175478336267/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8199/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175478336261/1000000000000 : ℝ) (175478336267/1000000000000 : ℝ) (58773916813/100000000000 : ℝ) (293869584067/500000000000 : ℝ) (83780268861/200000000000 : ℝ) (418901344313/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8199/65536 : ℝ))) 1 (58773916813/100000000000 : ℝ) (293869584067/500000000000 : ℝ) (83780268861/200000000000 : ℝ) (418901344313/1000000000000 : ℝ) (503320256217/1000000000000 : ℝ) (15728758007/31250000000 : ℝ) (248095106577/500000000000 : ℝ) (496190213161/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8199/65536 : ℝ))) 2 (503320256217/1000000000000 : ℝ) (15728758007/31250000000 : ℝ) (248095106577/500000000000 : ℝ) (496190213161/1000000000000 : ℝ) (99951046937/200000000000 : ℝ) (499755234693/1000000000000 : ℝ) (12493562973/25000000000 : ℝ) (31233907433/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8199/65536 : ℝ))) 3 (99951046937/200000000000 : ℝ) (499755234693/1000000000000 : ℝ) (12493562973/25000000000 : ℝ) (31233907433/62500000000 : ℝ) (249874438401/500000000000 : ℝ) (499748876811/1000000000000 : ℝ) (249874438381/500000000000 : ℝ) (499748876771/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8199/65536 : ℝ))) 4 (249874438401/500000000000 : ℝ) (499748876811/1000000000000 : ℝ) (249874438381/500000000000 : ℝ) (499748876771/1000000000000 : ℝ) (249874438391/500000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8199/65536 : ℝ))) 5 (249874438391/500000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8199/65536 : ℝ))) 6 (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8199/65536 : ℝ))) 7 (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8199/65536 : ℝ)) hmem 8 (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8199/65536 : ℝ))) hcmem 8 (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8199/65536 : ℝ)) (496113240179/500000000000 : ℝ) (496113240181/500000000000 : ℝ) (499748876781/1000000000000 : ℝ) (499748876791/1000000000000 : ℝ) (791153749173/1000000000000 : ℝ) (791153749193/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0196_exp_lower
  have heNumeric : (1027455116403/500000000000 : ℝ)/4 ≤ Real.exp (-5328497571669/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455116403/500000000000 : ℝ)/4 ≤ Real.exp ((4099/32768 : ℝ)-(791153749193/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4099/32768 : ℝ) (8199/65536 : ℝ) (791153749193/1000000000000 : ℝ) (1027455116403/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0197; no trusted numerical premise.
theorem cover8_leaf0197_exp_radius : (499023438741156393/500000000000000000 : ℝ) ≤ Real.exp ((-1025/65536 : ℝ)/8) ∧ Real.exp ((-1025/65536 : ℝ)/8) ≤ (998046877482312787/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1025/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0197_exp_lower : (920113910481850611/1000000000000000000 : ℝ) ≤ Real.exp ((-10656998510393/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656998510393/16000000000000 : ℝ)/8) ≤ (230028477620462653/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656998510393/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0197_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431862523/62500000000 : ℝ) ≤ 4*Real.exp (8199/65536 : ℝ)*Real.exp (-mu (radius 8 (1025/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (128431862523/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1025/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0197_exp_radius
  have hrNumeric : (61530088431/62500000000 : ℝ) ≤ Real.exp (-1025/65536 : ℝ) ∧ Real.exp (-1025/65536 : ℝ) ≤ (984481414897/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61530088431/62500000000 : ℝ) ≤ (radius 8 (1025/8192 : ℝ)) ∧ (radius 8 (1025/8192 : ℝ)) ≤ (984481414897/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1025/8192 : ℝ)) (61530088431/62500000000 : ℝ) (984481414897/1000000000000 : ℝ) (175488870651/1000000000000 : ℝ) (175488870657/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1025/8192 : ℝ)) (61530088431/62500000000 : ℝ) (984481414897/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1025/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61530088431/62500000000 : ℝ) (984481414897/1000000000000 : ℝ) (124030088431/125000000000 : ℝ) (992240707449/1000000000000 : ℝ) (496105184133/500000000000 : ℝ) (248052592067/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1025/8192 : ℝ)) 1 (124030088431/125000000000 : ℝ) (992240707449/1000000000000 : ℝ) (496105184133/500000000000 : ℝ) (248052592067/250000000000 : ℝ) (992225537857/1000000000000 : ℝ) (992225537859/1000000000000 : ℝ) (992225537741/1000000000000 : ℝ) (992225537743/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1025/8192 : ℝ)) 2 (992225537857/1000000000000 : ℝ) (992225537859/1000000000000 : ℝ) (992225537741/1000000000000 : ℝ) (992225537743/1000000000000 : ℝ) (992225537799/1000000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1025/8192 : ℝ)) 3 (992225537799/1000000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1025/8192 : ℝ)) 4 (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1025/8192 : ℝ)) 5 (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1025/8192 : ℝ)) 6 (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1025/8192 : ℝ)) 7 (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1025/8192 : ℝ))) (175488870651/1000000000000 : ℝ) (175488870657/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1025/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (175488870651/1000000000000 : ℝ) (175488870657/1000000000000 : ℝ) (23509777413/40000000000 : ℝ) (587744435329/1000000000000 : ℝ) (104728479487/250000000000 : ℝ) (104728479489/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1025/8192 : ℝ))) 1 (23509777413/40000000000 : ℝ) (587744435329/1000000000000 : ℝ) (104728479487/250000000000 : ℝ) (104728479489/250000000000 : ℝ) (125832294159/250000000000 : ℝ) (503329176643/1000000000000 : ℝ) (248099941633/500000000000 : ℝ) (248099941637/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1025/8192 : ℝ))) 2 (125832294159/250000000000 : ℝ) (503329176643/1000000000000 : ℝ) (248099941633/500000000000 : ℝ) (248099941637/500000000000 : ℝ) (499764529951/1000000000000 : ℝ) (499764529959/1000000000000 : ℝ) (62468977137/125000000000 : ℝ) (31234488569/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1025/8192 : ℝ))) 3 (499764529951/1000000000000 : ℝ) (499764529959/1000000000000 : ℝ) (62468977137/125000000000 : ℝ) (31234488569/62500000000 : ℝ) (499758173523/1000000000000 : ℝ) (124939543383/250000000000 : ℝ) (499758173483/1000000000000 : ℝ) (124939543373/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1025/8192 : ℝ))) 4 (499758173523/1000000000000 : ℝ) (124939543383/250000000000 : ℝ) (499758173483/1000000000000 : ℝ) (124939543373/250000000000 : ℝ) (499758173503/1000000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1025/8192 : ℝ))) 5 (499758173503/1000000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1025/8192 : ℝ))) 6 (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1025/8192 : ℝ))) 7 (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1025/8192 : ℝ)) hmem 8 (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1025/8192 : ℝ))) hcmem 8 (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1025/8192 : ℝ)) (496112768899/500000000000 : ℝ) (992225537801/1000000000000 : ℝ) (249879086751/500000000000 : ℝ) (62469771689/125000000000 : ℝ) (197792304601/250000000000 : ℝ) (791169218423/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0197_exp_lower
  have heNumeric : (128431862523/62500000000 : ℝ)/4 ≤ Real.exp (-10656998510393/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431862523/62500000000 : ℝ)/4 ≤ Real.exp ((8199/65536 : ℝ)-(791169218423/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8199/65536 : ℝ) (1025/8192 : ℝ) (791169218423/1000000000000 : ℝ) (128431862523/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0198; no trusted numerical premise.
theorem cover8_leaf0198_exp_radius : (499023319764711373/500000000000000000 : ℝ) ≤ Real.exp ((-8201/524288 : ℝ)/8) ∧ Real.exp ((-8201/524288 : ℝ)/8) ≤ (998046639529422747/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8201/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0198_exp_lower : (460056943212969991/500000000000000000 : ℝ) ≤ Real.exp ((-1332125232111/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332125232111/2000000000000 : ℝ)/8) ≤ (920113886425939983/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332125232111/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0198_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513727342643/250000000000 : ℝ) ≤ 4*Real.exp (1025/8192 : ℝ)*Real.exp (-mu (radius 8 (8201/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513727342643/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8201/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0198_exp_radius
  have hrNumeric : (984479537149/1000000000000 : ℝ) ≤ Real.exp (-8201/524288 : ℝ) ∧ Real.exp (-8201/524288 : ℝ) ≤ (19689590743/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984479537149/1000000000000 : ℝ) ≤ (radius 8 (8201/65536 : ℝ)) ∧ (radius 8 (8201/65536 : ℝ)) ≤ (19689590743/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8201/65536 : ℝ)) (984479537149/1000000000000 : ℝ) (19689590743/20000000000 : ℝ) (87749702183/500000000000 : ℝ) (43874851093/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8201/65536 : ℝ)) (984479537149/1000000000000 : ℝ) (19689590743/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8201/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984479537149/1000000000000 : ℝ) (19689590743/20000000000 : ℝ) (496119884287/500000000000 : ℝ) (39689590743/40000000000 : ℝ) (992209422021/1000000000000 : ℝ) (992209422023/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8201/65536 : ℝ)) 1 (496119884287/500000000000 : ℝ) (39689590743/40000000000 : ℝ) (992209422021/1000000000000 : ℝ) (992209422023/1000000000000 : ℝ) (992224595297/1000000000000 : ℝ) (992224595299/1000000000000 : ℝ) (992224595181/1000000000000 : ℝ) (992224595183/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8201/65536 : ℝ)) 2 (992224595297/1000000000000 : ℝ) (992224595299/1000000000000 : ℝ) (992224595181/1000000000000 : ℝ) (992224595183/1000000000000 : ℝ) (992224595239/1000000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8201/65536 : ℝ)) 3 (992224595239/1000000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8201/65536 : ℝ)) 4 (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8201/65536 : ℝ)) 5 (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8201/65536 : ℝ)) 6 (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8201/65536 : ℝ)) 7 (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8201/65536 : ℝ))) (87749702183/500000000000 : ℝ) (43874851093/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8201/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (87749702183/500000000000 : ℝ) (43874851093/250000000000 : ℝ) (587749702183/1000000000000 : ℝ) (293874851093/500000000000 : ℝ) (52365811301/125000000000 : ℝ) (26182905651/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8201/65536 : ℝ))) 1 (587749702183/1000000000000 : ℝ) (293874851093/500000000000 : ℝ) (52365811301/125000000000 : ℝ) (26182905651/62500000000 : ℝ) (100667619259/200000000000 : ℝ) (503338096301/1000000000000 : ℝ) (496209552481/1000000000000 : ℝ) (62026194061/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8201/65536 : ℝ))) 2 (100667619259/200000000000 : ℝ) (503338096301/1000000000000 : ℝ) (496209552481/1000000000000 : ℝ) (62026194061/125000000000 : ℝ) (124943456097/250000000000 : ℝ) (99954764879/200000000000 : ℝ) (249880557221/500000000000 : ℝ) (9995222289/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8201/65536 : ℝ))) 3 (124943456097/250000000000 : ℝ) (99954764879/200000000000 : ℝ) (249880557221/500000000000 : ℝ) (9995222289/20000000000 : ℝ) (99953493883/200000000000 : ℝ) (499767469423/1000000000000 : ℝ) (249883734687/500000000000 : ℝ) (499767469383/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8201/65536 : ℝ))) 4 (99953493883/200000000000 : ℝ) (499767469423/1000000000000 : ℝ) (249883734687/500000000000 : ℝ) (499767469383/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8201/65536 : ℝ))) 5 (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8201/65536 : ℝ))) 6 (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8201/65536 : ℝ))) 7 (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8201/65536 : ℝ)) hmem 8 (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8201/65536 : ℝ))) hcmem 8 (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8201/65536 : ℝ)) (496112297619/500000000000 : ℝ) (992224595241/1000000000000 : ℝ) (249883734697/500000000000 : ℝ) (499767469403/1000000000000 : ℝ) (791184686351/1000000000000 : ℝ) (24724521449/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0198_exp_lower
  have heNumeric : (513727342643/250000000000 : ℝ)/4 ≤ Real.exp (-1332125232111/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513727342643/250000000000 : ℝ)/4 ≤ Real.exp ((1025/8192 : ℝ)-(24724521449/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1025/8192 : ℝ) (8201/65536 : ℝ) (24724521449/31250000000 : ℝ) (513727342643/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0199; no trusted numerical premise.
theorem cover8_leaf0199_exp_radius : (499023200788294719/500000000000000000 : ℝ) ≤ Real.exp ((-4101/262144 : ℝ)/8) ∧ Real.exp ((-4101/262144 : ℝ)/8) ≤ (998046401576589439/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4101/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0199_exp_lower : (460056931258394071/500000000000000000 : ℝ) ≤ Real.exp ((-10657005182967/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657005182967/16000000000000 : ℝ)/8) ≤ (920113862516788143/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657005182967/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0199_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054908943397/1000000000000 : ℝ) ≤ 4*Real.exp (8201/65536 : ℝ)*Real.exp (-mu (radius 8 (4101/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054908943397/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4101/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0199_exp_radius
  have hrNumeric : (196895531881/200000000000 : ℝ) ≤ Real.exp (-4101/262144 : ℝ) ∧ Real.exp (-4101/262144 : ℝ) ≤ (492238829703/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196895531881/200000000000 : ℝ) ≤ (radius 8 (4101/32768 : ℝ)) ∧ (radius 8 (4101/32768 : ℝ)) ≤ (492238829703/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4101/32768 : ℝ)) (196895531881/200000000000 : ℝ) (492238829703/500000000000 : ℝ) (43877484353/250000000000 : ℝ) (87754968709/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4101/32768 : ℝ)) (196895531881/200000000000 : ℝ) (492238829703/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4101/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196895531881/200000000000 : ℝ) (492238829703/500000000000 : ℝ) (496119414851/500000000000 : ℝ) (992238829703/1000000000000 : ℝ) (992208475777/1000000000000 : ℝ) (992208475779/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4101/32768 : ℝ)) 1 (496119414851/500000000000 : ℝ) (992238829703/1000000000000 : ℝ) (992208475777/1000000000000 : ℝ) (992208475779/1000000000000 : ℝ) (992223652739/1000000000000 : ℝ) (992223652741/1000000000000 : ℝ) (992223652623/1000000000000 : ℝ) (7937789221/8000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4101/32768 : ℝ)) 2 (992223652739/1000000000000 : ℝ) (992223652741/1000000000000 : ℝ) (992223652623/1000000000000 : ℝ) (7937789221/8000000000 : ℝ) (992223652681/1000000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4101/32768 : ℝ)) 3 (992223652681/1000000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4101/32768 : ℝ)) 4 (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4101/32768 : ℝ)) 5 (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4101/32768 : ℝ)) 6 (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4101/32768 : ℝ)) 7 (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4101/32768 : ℝ))) (43877484353/250000000000 : ℝ) (87754968709/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4101/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (43877484353/250000000000 : ℝ) (87754968709/500000000000 : ℝ) (293877484353/500000000000 : ℝ) (587754968709/1000000000000 : ℝ) (104734765423/250000000000 : ℝ) (4189390617/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4101/32768 : ℝ))) 1 (293877484353/500000000000 : ℝ) (587754968709/1000000000000 : ℝ) (104734765423/250000000000 : ℝ) (4189390617/10000000000 : ℝ) (503347015199/1000000000000 : ℝ) (100669403041/200000000000 : ℝ) (496219220803/1000000000000 : ℝ) (49621922081/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4101/32768 : ℝ))) 2 (503347015199/1000000000000 : ℝ) (100669403041/200000000000 : ℝ) (496219220803/1000000000000 : ℝ) (49621922081/100000000000 : ℝ) (499783118001/1000000000000 : ℝ) (62472889751/125000000000 : ℝ) (124942602741/250000000000 : ℝ) (499770410971/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4101/32768 : ℝ))) 3 (499783118001/1000000000000 : ℝ) (62472889751/125000000000 : ℝ) (124942602741/250000000000 : ℝ) (499770410971/1000000000000 : ℝ) (249888382241/500000000000 : ℝ) (49977676449/100000000000 : ℝ) (249888382221/500000000000 : ℝ) (9995535289/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4101/32768 : ℝ))) 4 (249888382241/500000000000 : ℝ) (49977676449/100000000000 : ℝ) (249888382221/500000000000 : ℝ) (9995535289/20000000000 : ℝ) (249888382231/500000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4101/32768 : ℝ))) 5 (249888382231/500000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4101/32768 : ℝ))) 6 (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4101/32768 : ℝ))) 7 (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4101/32768 : ℝ)) hmem 8 (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4101/32768 : ℝ))) hcmem 8 (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4101/32768 : ℝ)) (24805591317/25000000000 : ℝ) (992223652683/1000000000000 : ℝ) (499776764461/1000000000000 : ℝ) (49977676447/100000000000 : ℝ) (791200153019/1000000000000 : ℝ) (791200153037/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0199_exp_lower
  have heNumeric : (2054908943397/1000000000000 : ℝ)/4 ≤ Real.exp (-10657005182967/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054908943397/1000000000000 : ℝ)/4 ≤ Real.exp ((8201/65536 : ℝ)-(791200153037/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8201/65536 : ℝ) (4101/32768 : ℝ) (791200153037/1000000000000 : ℝ) (2054908943397/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0175_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0175_certificate
#check SmaleRate.Proofs.cover8_leaf0176_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0176_certificate
#check SmaleRate.Proofs.cover8_leaf0177_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0177_certificate
#check SmaleRate.Proofs.cover8_leaf0178_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0178_certificate
#check SmaleRate.Proofs.cover8_leaf0179_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0179_certificate
#check SmaleRate.Proofs.cover8_leaf0180_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0180_certificate
#check SmaleRate.Proofs.cover8_leaf0181_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0181_certificate
#check SmaleRate.Proofs.cover8_leaf0182_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0182_certificate
#check SmaleRate.Proofs.cover8_leaf0183_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0183_certificate
#check SmaleRate.Proofs.cover8_leaf0184_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0184_certificate
#check SmaleRate.Proofs.cover8_leaf0185_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0185_certificate
#check SmaleRate.Proofs.cover8_leaf0186_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0186_certificate
#check SmaleRate.Proofs.cover8_leaf0187_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0187_certificate
#check SmaleRate.Proofs.cover8_leaf0188_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0188_certificate
#check SmaleRate.Proofs.cover8_leaf0189_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0189_certificate
#check SmaleRate.Proofs.cover8_leaf0190_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0190_certificate
#check SmaleRate.Proofs.cover8_leaf0191_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0191_certificate
#check SmaleRate.Proofs.cover8_leaf0192_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0192_certificate
#check SmaleRate.Proofs.cover8_leaf0193_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0193_certificate
#check SmaleRate.Proofs.cover8_leaf0194_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0194_certificate
#check SmaleRate.Proofs.cover8_leaf0195_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0195_certificate
#check SmaleRate.Proofs.cover8_leaf0196_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0196_certificate
#check SmaleRate.Proofs.cover8_leaf0197_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0197_certificate
#check SmaleRate.Proofs.cover8_leaf0198_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0198_certificate
#check SmaleRate.Proofs.cover8_leaf0199_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0199_certificate
