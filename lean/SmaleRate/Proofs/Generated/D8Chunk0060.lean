/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1500; no trusted numerical premise.
theorem cover8_leaf1500_exp_radius : (997973114803531403/1000000000000000000 : ℝ) ≤ Real.exp ((-4255/262144 : ℝ)/8) ∧ Real.exp ((-4255/262144 : ℝ)/8) ≤ (249493278700882851/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4255/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1500_exp_lower : (460057118779062567/500000000000000000 : ℝ) ≤ Real.exp ((-21313906019541/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313906019541/32000000000000 : ℝ)/8) ≤ (184022847511625027/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313906019541/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1500_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027457822053/500000000000 : ℝ) ≤ 4*Real.exp (17019/131072 : ℝ)*Real.exp (-mu (radius 8 (4255/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027457822053/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4255/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1500_exp_radius
  have hrNumeric : (983899484677/1000000000000 : ℝ) ≤ Real.exp (-4255/262144 : ℝ) ∧ Real.exp (-4255/262144 : ℝ) ≤ (491949742339/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983899484677/1000000000000 : ℝ) ≤ (radius 8 (4255/32768 : ℝ)) ∧ (radius 8 (4255/32768 : ℝ)) ≤ (491949742339/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4255/32768 : ℝ)) (983899484677/1000000000000 : ℝ) (491949742339/500000000000 : ℝ) (11170168847/62500000000 : ℝ) (178722701559/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4255/32768 : ℝ)) (983899484677/1000000000000 : ℝ) (491949742339/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4255/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983899484677/1000000000000 : ℝ) (491949742339/500000000000 : ℝ) (495974871169/500000000000 : ℝ) (991949742339/1000000000000 : ℝ) (61994817219/62500000000 : ℝ) (198383415101/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4255/32768 : ℝ)) 1 (495974871169/500000000000 : ℝ) (991949742339/1000000000000 : ℝ) (61994817219/62500000000 : ℝ) (198383415101/200000000000 : ℝ) (991933408921/1000000000000 : ℝ) (495966704461/500000000000 : ℝ) (495966704393/500000000000 : ℝ) (247983352197/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4255/32768 : ℝ)) 2 (991933408921/1000000000000 : ℝ) (495966704461/500000000000 : ℝ) (495966704393/500000000000 : ℝ) (247983352197/250000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4255/32768 : ℝ)) 3 (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4255/32768 : ℝ)) 4 (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4255/32768 : ℝ)) 5 (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4255/32768 : ℝ)) 6 (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4255/32768 : ℝ)) 7 (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4255/32768 : ℝ))) (11170168847/62500000000 : ℝ) (178722701559/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4255/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11170168847/62500000000 : ℝ) (178722701559/1000000000000 : ℝ) (73670168847/125000000000 : ℝ) (29468067539/50000000000 : ℝ) (211378039039/500000000000 : ℝ) (422756078087/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4255/32768 : ℝ))) 1 (73670168847/125000000000 : ℝ) (29468067539/50000000000 : ℝ) (211378039039/500000000000 : ℝ) (422756078087/1000000000000 : ℝ) (506058714427/1000000000000 : ℝ) (253029357217/500000000000 : ℝ) (499155379841/1000000000000 : ℝ) (499155379849/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4255/32768 : ℝ))) 2 (506058714427/1000000000000 : ℝ) (253029357217/500000000000 : ℝ) (499155379841/1000000000000 : ℝ) (499155379849/1000000000000 : ℝ) (251303523567/500000000000 : ℝ) (251303523571/500000000000 : ℝ) (100519038957/200000000000 : ℝ) (251297597397/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4255/32768 : ℝ))) 3 (251303523567/500000000000 : ℝ) (251303523571/500000000000 : ℝ) (100519038957/200000000000 : ℝ) (251297597397/500000000000 : ℝ) (502601120959/1000000000000 : ℝ) (62825140121/125000000000 : ℝ) (125650280231/250000000000 : ℝ) (251300560467/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4255/32768 : ℝ))) 4 (502601120959/1000000000000 : ℝ) (62825140121/125000000000 : ℝ) (125650280231/250000000000 : ℝ) (251300560467/500000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4255/32768 : ℝ))) 5 (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4255/32768 : ℝ))) 6 (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4255/32768 : ℝ))) 7 (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4255/32768 : ℝ)) hmem 8 (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4255/32768 : ℝ))) hcmem 8 (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4255/32768 : ℝ)) (991933408853/1000000000000 : ℝ) (198386681771/200000000000 : ℝ) (502601120941/1000000000000 : ℝ) (502601120951/1000000000000 : ℝ) (795904228619/1000000000000 : ℝ) (397952114319/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1500_exp_lower
  have heNumeric : (1027457822053/500000000000 : ℝ)/4 ≤ Real.exp (-21313906019541/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027457822053/500000000000 : ℝ)/4 ≤ Real.exp ((17019/131072 : ℝ)-(397952114319/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17019/131072 : ℝ) (4255/32768 : ℝ) (397952114319/500000000000 : ℝ) (1027457822053/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1501; no trusted numerical premise.
theorem cover8_leaf1501_exp_radius : (498986438434113877/500000000000000000 : ℝ) ≤ Real.exp ((-8511/524288 : ℝ)/8) ∧ Real.exp ((-8511/524288 : ℝ)/8) ≤ (199594575373645551/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8511/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1501_exp_lower : (920113380237889269/1000000000000000000 : ℝ) ≤ Real.exp ((-5328536137177/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328536137177/8000000000000 : ℝ)/8) ≤ (92011338023788927/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328536137177/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1501_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900326747/1000000000000 : ℝ) ≤ 4*Real.exp (4255/32768 : ℝ)*Real.exp (-mu (radius 8 (8511/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900326747/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8511/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1501_exp_radius
  have hrNumeric : (24597440201/25000000000 : ℝ) ≤ Real.exp (-8511/524288 : ℝ) ∧ Real.exp (-8511/524288 : ℝ) ≤ (983897608041/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24597440201/25000000000 : ℝ) ≤ (radius 8 (8511/65536 : ℝ)) ∧ (radius 8 (8511/65536 : ℝ)) ≤ (983897608041/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8511/65536 : ℝ)) (24597440201/25000000000 : ℝ) (983897608041/1000000000000 : ℝ) (22341629057/125000000000 : ℝ) (178733032463/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8511/65536 : ℝ)) (24597440201/25000000000 : ℝ) (983897608041/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8511/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24597440201/25000000000 : ℝ) (983897608041/1000000000000 : ℝ) (49597440201/50000000000 : ℝ) (991948804021/1000000000000 : ℝ) (991916129539/1000000000000 : ℝ) (49595806477/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8511/65536 : ℝ)) 1 (49597440201/50000000000 : ℝ) (991948804021/1000000000000 : ℝ) (991916129539/1000000000000 : ℝ) (49595806477/50000000000 : ℝ) (991932466779/1000000000000 : ℝ) (991932466781/1000000000000 : ℝ) (247983116661/250000000000 : ℝ) (495966233323/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8511/65536 : ℝ)) 2 (991932466779/1000000000000 : ℝ) (991932466781/1000000000000 : ℝ) (247983116661/250000000000 : ℝ) (495966233323/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8511/65536 : ℝ)) 3 (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8511/65536 : ℝ)) 4 (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8511/65536 : ℝ)) 5 (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8511/65536 : ℝ)) 6 (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8511/65536 : ℝ)) 7 (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8511/65536 : ℝ))) (22341629057/125000000000 : ℝ) (178733032463/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8511/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22341629057/125000000000 : ℝ) (178733032463/1000000000000 : ℝ) (147341629057/250000000000 : ℝ) (73670814529/125000000000 : ℝ) (422768296417/1000000000000 : ℝ) (422768296427/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8511/65536 : ℝ))) 1 (147341629057/250000000000 : ℝ) (73670814529/125000000000 : ℝ) (422768296417/1000000000000 : ℝ) (422768296427/1000000000000 : ℝ) (253033703161/500000000000 : ℝ) (50606740633/100000000000 : ℝ) (499164780439/1000000000000 : ℝ) (499164780447/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8511/65536 : ℝ))) 2 (253033703161/500000000000 : ℝ) (50606740633/100000000000 : ℝ) (499164780439/1000000000000 : ℝ) (499164780447/1000000000000 : ℝ) (25130804669/50000000000 : ℝ) (502616093389/1000000000000 : ℝ) (251302121839/500000000000 : ℝ) (502604243687/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8511/65536 : ℝ))) 3 (25130804669/50000000000 : ℝ) (502616093389/1000000000000 : ℝ) (251302121839/500000000000 : ℝ) (502604243687/1000000000000 : ℝ) (502610168529/1000000000000 : ℝ) (251305084269/500000000000 : ℝ) (251305084247/500000000000 : ℝ) (62826271063/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8511/65536 : ℝ))) 4 (502610168529/1000000000000 : ℝ) (251305084269/500000000000 : ℝ) (251305084247/500000000000 : ℝ) (62826271063/125000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8511/65536 : ℝ))) 5 (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8511/65536 : ℝ))) 6 (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8511/65536 : ℝ))) 7 (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8511/65536 : ℝ)) hmem 8 (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8511/65536 : ℝ))) hcmem 8 (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8511/65536 : ℝ)) (991932466711/1000000000000 : ℝ) (495966233357/500000000000 : ℝ) (502610168511/1000000000000 : ℝ) (502610168521/1000000000000 : ℝ) (795919312049/1000000000000 : ℝ) (795919312069/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1501_exp_lower
  have heNumeric : (2054900326747/1000000000000 : ℝ)/4 ≤ Real.exp (-5328536137177/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900326747/1000000000000 : ℝ)/4 ≤ Real.exp ((4255/32768 : ℝ)-(795919312069/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4255/32768 : ℝ) (8511/65536 : ℝ) (795919312069/1000000000000 : ℝ) (2054900326747/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1502; no trusted numerical premise.
theorem cover8_leaf1502_exp_radius : (997972638932980833/1000000000000000000 : ℝ) ≤ Real.exp ((-133/8192 : ℝ)/8) ∧ Real.exp ((-133/8192 : ℝ)/8) ≤ (498986319466490417/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1502_exp_lower : (115014175068027989/125000000000000000 : ℝ) ≤ Real.exp ((-10657069449473/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657069449473/16000000000000 : ℝ)/8) ≤ (920113400544223913/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657069449473/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1502_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098013791/20000000000 : ℝ) ≤ 4*Real.exp (8511/65536 : ℝ)*Real.exp (-mu (radius 8 (133/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (41098013791/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (133/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1502_exp_radius
  have hrNumeric : (491947865703/500000000000 : ℝ) ≤ Real.exp (-133/8192 : ℝ) ∧ Real.exp (-133/8192 : ℝ) ≤ (983895731407/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491947865703/500000000000 : ℝ) ≤ (radius 8 (133/1024 : ℝ)) ∧ (radius 8 (133/1024 : ℝ)) ≤ (983895731407/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (133/1024 : ℝ)) (491947865703/500000000000 : ℝ) (983895731407/1000000000000 : ℝ) (178743362727/1000000000000 : ℝ) (178743362733/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (133/1024 : ℝ)) (491947865703/500000000000 : ℝ) (983895731407/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (133/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491947865703/500000000000 : ℝ) (983895731407/1000000000000 : ℝ) (991947865703/1000000000000 : ℝ) (123993483213/125000000000 : ℝ) (495957591787/500000000000 : ℝ) (123989397947/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (133/1024 : ℝ)) 1 (991947865703/1000000000000 : ℝ) (123993483213/125000000000 : ℝ) (495957591787/500000000000 : ℝ) (123989397947/125000000000 : ℝ) (495965762319/500000000000 : ℝ) (6199572029/6250000000 : ℝ) (991931524503/1000000000000 : ℝ) (495965762253/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (133/1024 : ℝ)) 2 (495965762319/500000000000 : ℝ) (6199572029/6250000000 : ℝ) (991931524503/1000000000000 : ℝ) (495965762253/500000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (133/1024 : ℝ)) 3 (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (133/1024 : ℝ)) 4 (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (133/1024 : ℝ)) 5 (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (133/1024 : ℝ)) 6 (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (133/1024 : ℝ)) 7 (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (133/1024 : ℝ))) (178743362727/1000000000000 : ℝ) (178743362733/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (133/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178743362727/1000000000000 : ℝ) (178743362733/1000000000000 : ℝ) (589371681363/1000000000000 : ℝ) (589371681367/1000000000000 : ℝ) (84556102731/200000000000 : ℝ) (422780513663/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (133/1024 : ℝ))) 1 (589371681363/1000000000000 : ℝ) (589371681367/1000000000000 : ℝ) (84556102731/200000000000 : ℝ) (422780513663/1000000000000 : ℝ) (506076097509/1000000000000 : ℝ) (101215219503/200000000000 : ℝ) (249587090101/500000000000 : ℝ) (499174180209/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (133/1024 : ℝ))) 2 (506076097509/1000000000000 : ℝ) (101215219503/200000000000 : ℝ) (249587090101/500000000000 : ℝ) (499174180209/1000000000000 : ℝ) (100525027771/200000000000 : ℝ) (251312569431/500000000000 : ℝ) (502613291799/1000000000000 : ℝ) (502613291807/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (133/1024 : ℝ))) 3 (100525027771/200000000000 : ℝ) (251312569431/500000000000 : ℝ) (502613291799/1000000000000 : ℝ) (502613291807/1000000000000 : ℝ) (502619215327/1000000000000 : ℝ) (100523843067/200000000000 : ℝ) (125654803823/250000000000 : ℝ) (5026192153/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (133/1024 : ℝ))) 4 (502619215327/1000000000000 : ℝ) (100523843067/200000000000 : ℝ) (125654803823/250000000000 : ℝ) (5026192153/10000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (133/1024 : ℝ))) 5 (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (133/1024 : ℝ))) 6 (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (133/1024 : ℝ))) 7 (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (133/1024 : ℝ)) hmem 8 (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (133/1024 : ℝ))) hcmem 8 (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (133/1024 : ℝ)) (99193152457/100000000000 : ℝ) (991931524573/1000000000000 : ℝ) (502619215309/1000000000000 : ℝ) (251309607659/500000000000 : ℝ) (159186878857/200000000000 : ℝ) (795934394303/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1502_exp_lower
  have heNumeric : (41098013791/20000000000 : ℝ)/4 ≤ Real.exp (-10657069449473/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098013791/20000000000 : ℝ)/4 ≤ Real.exp ((8511/65536 : ℝ)-(795934394303/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8511/65536 : ℝ) (133/1024 : ℝ) (795934394303/1000000000000 : ℝ) (41098013791/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1503; no trusted numerical premise.
theorem cover8_leaf1503_exp_radius : (997972400997790641/1000000000000000000 : ℝ) ≤ Real.exp ((-8513/524288 : ℝ)/8) ∧ Real.exp ((-8513/524288 : ℝ)/8) ≤ (498986200498895321/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8513/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1503_exp_lower : (230028355246971483/250000000000000000 : ℝ) ≤ Real.exp ((-666066662843/1000000000000 : ℝ)/8) ∧ Real.exp ((-666066662843/1000000000000 : ℝ)/8) ≤ (920113420987885933/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666066662843/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1503_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901054807/1000000000000 : ℝ) ≤ 4*Real.exp (133/1024 : ℝ)*Real.exp (-mu (radius 8 (8513/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901054807/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8513/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1503_exp_radius
  have hrNumeric : (39355754191/40000000000 : ℝ) ≤ Real.exp (-8513/524288 : ℝ) ∧ Real.exp (-8513/524288 : ℝ) ≤ (122986731847/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39355754191/40000000000 : ℝ) ≤ (radius 8 (8513/65536 : ℝ)) ∧ (radius 8 (8513/65536 : ℝ)) ≤ (122986731847/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8513/65536 : ℝ)) (39355754191/40000000000 : ℝ) (122986731847/125000000000 : ℝ) (44688423091/250000000000 : ℝ) (178753692371/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8513/65536 : ℝ)) (39355754191/40000000000 : ℝ) (122986731847/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8513/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39355754191/40000000000 : ℝ) (122986731847/125000000000 : ℝ) (991946927387/1000000000000 : ℝ) (247986731847/250000000000 : ℝ) (99191423761/100000000000 : ℝ) (247978559403/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8513/65536 : ℝ)) 1 (991946927387/1000000000000 : ℝ) (247986731847/250000000000 : ℝ) (99191423761/100000000000 : ℝ) (247978559403/250000000000 : ℝ) (495965291249/500000000000 : ℝ) (396772233/400000000 : ℝ) (991930582363/1000000000000 : ℝ) (495965291183/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8513/65536 : ℝ)) 2 (495965291249/500000000000 : ℝ) (396772233/400000000 : ℝ) (991930582363/1000000000000 : ℝ) (495965291183/500000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8513/65536 : ℝ)) 3 (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8513/65536 : ℝ)) 4 (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8513/65536 : ℝ)) 5 (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8513/65536 : ℝ)) 6 (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8513/65536 : ℝ)) 7 (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8513/65536 : ℝ))) (44688423091/250000000000 : ℝ) (178753692371/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8513/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44688423091/250000000000 : ℝ) (178753692371/1000000000000 : ℝ) (294688423091/500000000000 : ℝ) (294688423093/500000000000 : ℝ) (42279272979/100000000000 : ℝ) (2113963649/5000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8513/65536 : ℝ))) 1 (294688423091/500000000000 : ℝ) (294688423093/500000000000 : ℝ) (42279272979/100000000000 : ℝ) (2113963649/5000000000 : ℝ) (253042393993/500000000000 : ℝ) (506084787993/1000000000000 : ℝ) (499183579129/1000000000000 : ℝ) (499183579137/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8513/65536 : ℝ))) 2 (253042393993/500000000000 : ℝ) (506084787993/1000000000000 : ℝ) (499183579129/1000000000000 : ℝ) (499183579137/1000000000000 : ℝ) (502634183557/1000000000000 : ℝ) (100526836713/200000000000 : ℝ) (251311169573/500000000000 : ℝ) (100524467831/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8513/65536 : ℝ))) 3 (502634183557/1000000000000 : ℝ) (100526836713/200000000000 : ℝ) (251311169573/500000000000 : ℝ) (100524467831/200000000000 : ℝ) (502628261351/1000000000000 : ℝ) (6282853267/12500000000 : ℝ) (125657065329/250000000000 : ℝ) (251314130663/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8513/65536 : ℝ))) 4 (502628261351/1000000000000 : ℝ) (6282853267/12500000000 : ℝ) (125657065329/250000000000 : ℝ) (251314130663/500000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8513/65536 : ℝ))) 5 (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8513/65536 : ℝ))) 6 (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8513/65536 : ℝ))) 7 (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8513/65536 : ℝ)) hmem 8 (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8513/65536 : ℝ))) hcmem 8 (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8513/65536 : ℝ)) (99193058243/100000000000 : ℝ) (991930582433/1000000000000 : ℝ) (502628261333/1000000000000 : ℝ) (502628261343/1000000000000 : ℝ) (795949475323/1000000000000 : ℝ) (795949475343/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1503_exp_lower
  have heNumeric : (2054901054807/1000000000000 : ℝ)/4 ≤ Real.exp (-666066662843/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901054807/1000000000000 : ℝ)/4 ≤ Real.exp ((133/1024 : ℝ)-(795949475343/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (133/1024 : ℝ) (8513/65536 : ℝ) (795949475343/1000000000000 : ℝ) (2054901054807/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1504; no trusted numerical premise.
theorem cover8_leaf1504_exp_radius : (997972163062657177/1000000000000000000 : ℝ) ≤ Real.exp ((-4257/262144 : ℝ)/8) ∧ Real.exp ((-4257/262144 : ℝ)/8) ≤ (498986081531328589/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4257/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1504_exp_lower : (46005672078558781/50000000000000000 : ℝ) ≤ Real.exp ((-10657063742079/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657063742079/16000000000000 : ℝ)/8) ≤ (920113441571175621/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657063742079/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1504_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450711279/500000000000 : ℝ) ≤ 4*Real.exp (8513/65536 : ℝ)*Real.exp (-mu (radius 8 (4257/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450711279/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4257/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1504_exp_radius
  have hrNumeric : (983891978149/1000000000000 : ℝ) ≤ Real.exp (-4257/262144 : ℝ) ∧ Real.exp (-4257/262144 : ℝ) ≤ (19677839563/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983891978149/1000000000000 : ℝ) ≤ (radius 8 (4257/32768 : ℝ)) ∧ (radius 8 (4257/32768 : ℝ)) ≤ (19677839563/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4257/32768 : ℝ)) (983891978149/1000000000000 : ℝ) (19677839563/20000000000 : ℝ) (178764021357/1000000000000 : ℝ) (44691005341/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4257/32768 : ℝ)) (983891978149/1000000000000 : ℝ) (19677839563/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4257/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983891978149/1000000000000 : ℝ) (19677839563/20000000000 : ℝ) (495972994537/500000000000 : ℝ) (39677839563/40000000000 : ℝ) (7749322591/7812500000 : ℝ) (19838265833/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4257/32768 : ℝ)) 1 (495972994537/500000000000 : ℝ) (39677839563/40000000000 : ℝ) (7749322591/7812500000 : ℝ) (19838265833/20000000000 : ℝ) (991929640361/1000000000000 : ℝ) (991929640363/1000000000000 : ℝ) (495964820113/500000000000 : ℝ) (247982410057/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4257/32768 : ℝ)) 2 (991929640361/1000000000000 : ℝ) (991929640363/1000000000000 : ℝ) (495964820113/500000000000 : ℝ) (247982410057/250000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4257/32768 : ℝ)) 3 (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4257/32768 : ℝ)) 4 (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4257/32768 : ℝ)) 5 (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4257/32768 : ℝ)) 6 (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4257/32768 : ℝ)) 7 (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4257/32768 : ℝ))) (178764021357/1000000000000 : ℝ) (44691005341/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4257/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178764021357/1000000000000 : ℝ) (44691005341/250000000000 : ℝ) (294691005339/500000000000 : ℝ) (294691005341/500000000000 : ℝ) (422804944811/1000000000000 : ℝ) (21140247241/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4257/32768 : ℝ))) 1 (294691005339/500000000000 : ℝ) (294691005341/500000000000 : ℝ) (422804944811/1000000000000 : ℝ) (21140247241/50000000000 : ℝ) (31630842359/62500000000 : ℝ) (506093477751/1000000000000 : ℝ) (499192977211/1000000000000 : ℝ) (499192977219/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4257/32768 : ℝ))) 2 (31630842359/62500000000 : ℝ) (506093477751/1000000000000 : ℝ) (499192977211/1000000000000 : ℝ) (499192977219/1000000000000 : ℝ) (502643227477/1000000000000 : ℝ) (100528645497/200000000000 : ℝ) (502631385711/1000000000000 : ℝ) (502631385719/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4257/32768 : ℝ))) 3 (502643227477/1000000000000 : ℝ) (100528645497/200000000000 : ℝ) (502631385711/1000000000000 : ℝ) (502631385719/1000000000000 : ℝ) (251318653297/500000000000 : ℝ) (251318653301/500000000000 : ℝ) (502637306559/1000000000000 : ℝ) (62829663321/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4257/32768 : ℝ))) 4 (251318653297/500000000000 : ℝ) (251318653301/500000000000 : ℝ) (502637306559/1000000000000 : ℝ) (62829663321/125000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4257/32768 : ℝ))) 5 (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4257/32768 : ℝ))) 6 (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4257/32768 : ℝ))) 7 (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4257/32768 : ℝ)) hmem 8 (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4257/32768 : ℝ))) hcmem 8 (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4257/32768 : ℝ)) (991929640293/1000000000000 : ℝ) (123991205037/125000000000 : ℝ) (31414831661/62500000000 : ℝ) (100527461317/200000000000 : ℝ) (795964555151/1000000000000 : ℝ) (795964555169/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1504_exp_lower
  have heNumeric : (1027450711279/500000000000 : ℝ)/4 ≤ Real.exp (-10657063742079/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450711279/500000000000 : ℝ)/4 ≤ Real.exp ((8513/65536 : ℝ)-(795964555169/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8513/65536 : ℝ) (4257/32768 : ℝ) (795964555169/1000000000000 : ℝ) (1027450711279/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1505; no trusted numerical premise.
theorem cover8_leaf1505_exp_radius : (24949298128189511/25000000000000000 : ℝ) ≤ Real.exp ((-8515/524288 : ℝ)/8) ∧ Real.exp ((-8515/524288 : ℝ)/8) ≤ (997971925127580441/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8515/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1505_exp_lower : (115014182786344697/125000000000000000 : ℝ) ≤ Real.exp ((-1065706085971/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065706085971/1600000000000 : ℝ)/8) ≤ (920113462290757577/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065706085971/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1505_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980358549/200000000000 : ℝ) ≤ 4*Real.exp (4257/32768 : ℝ)*Real.exp (-mu (radius 8 (8515/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410980358549/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8515/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1505_exp_radius
  have hrNumeric : (39355604061/40000000000 : ℝ) ≤ Real.exp (-8515/524288 : ℝ) ∧ Real.exp (-8515/524288 : ℝ) ≤ (491945050763/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39355604061/40000000000 : ℝ) ≤ (radius 8 (8515/65536 : ℝ)) ∧ (radius 8 (8515/65536 : ℝ)) ≤ (491945050763/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8515/65536 : ℝ)) (39355604061/40000000000 : ℝ) (491945050763/500000000000 : ℝ) (178774349723/1000000000000 : ℝ) (17877434973/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8515/65536 : ℝ)) (39355604061/40000000000 : ℝ) (491945050763/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8515/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39355604061/40000000000 : ℝ) (491945050763/500000000000 : ℝ) (495972525381/500000000000 : ℝ) (991945050763/1000000000000 : ℝ) (495956172843/500000000000 : ℝ) (991912345687/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8515/65536 : ℝ)) 1 (495972525381/500000000000 : ℝ) (991945050763/1000000000000 : ℝ) (495956172843/500000000000 : ℝ) (991912345687/1000000000000 : ℝ) (61995543639/62500000000 : ℝ) (39677147929/40000000000 : ℝ) (991928698089/1000000000000 : ℝ) (991928698091/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8515/65536 : ℝ)) 2 (61995543639/62500000000 : ℝ) (39677147929/40000000000 : ℝ) (991928698089/1000000000000 : ℝ) (991928698091/1000000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8515/65536 : ℝ)) 3 (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8515/65536 : ℝ)) 4 (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8515/65536 : ℝ)) 5 (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8515/65536 : ℝ)) 6 (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8515/65536 : ℝ)) 7 (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8515/65536 : ℝ))) (178774349723/1000000000000 : ℝ) (17877434973/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8515/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178774349723/1000000000000 : ℝ) (17877434973/100000000000 : ℝ) (589387174861/1000000000000 : ℝ) (117877434973/200000000000 : ℝ) (422817158737/1000000000000 : ℝ) (211408579373/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8515/65536 : ℝ))) 1 (589387174861/1000000000000 : ℝ) (117877434973/200000000000 : ℝ) (422817158737/1000000000000 : ℝ) (211408579373/500000000000 : ℝ) (506102166799/1000000000000 : ℝ) (253051083403/500000000000 : ℝ) (7800037101/15625000000 : ℝ) (62400296809/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8515/65536 : ℝ))) 2 (506102166799/1000000000000 : ℝ) (253051083403/500000000000 : ℝ) (7800037101/15625000000 : ℝ) (62400296809/125000000000 : ℝ) (502652270631/1000000000000 : ℝ) (502652270639/1000000000000 : ℝ) (125660107877/250000000000 : ℝ) (502640431517/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8515/65536 : ℝ))) 3 (502652270631/1000000000000 : ℝ) (502652270639/1000000000000 : ℝ) (125660107877/250000000000 : ℝ) (502640431517/1000000000000 : ℝ) (502646351069/1000000000000 : ℝ) (251323175539/500000000000 : ℝ) (251323175517/500000000000 : ℝ) (125661587761/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8515/65536 : ℝ))) 4 (502646351069/1000000000000 : ℝ) (251323175539/500000000000 : ℝ) (251323175517/500000000000 : ℝ) (125661587761/250000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8515/65536 : ℝ))) 5 (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8515/65536 : ℝ))) 6 (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8515/65536 : ℝ))) 7 (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8515/65536 : ℝ)) hmem 8 (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8515/65536 : ℝ))) hcmem 8 (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8515/65536 : ℝ)) (247982174539/250000000000 : ℝ) (495964349079/500000000000 : ℝ) (502646351051/1000000000000 : ℝ) (502646351061/1000000000000 : ℝ) (6218590889/7812500000 : ℝ) (79597963381/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1505_exp_lower
  have heNumeric : (410980358549/200000000000 : ℝ)/4 ≤ Real.exp (-1065706085971/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980358549/200000000000 : ℝ)/4 ≤ Real.exp ((4257/32768 : ℝ)-(79597963381/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4257/32768 : ℝ) (8515/65536 : ℝ) (79597963381/100000000000 : ℝ) (410980358549/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1506; no trusted numerical premise.
theorem cover8_leaf1506_exp_radius : (62373230449535027/62500000000000000 : ℝ) ≤ Real.exp ((-2129/131072 : ℝ)/8) ∧ Real.exp ((-2129/131072 : ℝ)/8) ≤ (997971687192560433/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2129/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1506_exp_lower : (920113483149622177/1000000000000000000 : ℝ) ≤ Real.exp ((-2131411591593/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131411591593/3200000000000 : ℝ)/8) ≤ (460056741574811089/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131411591593/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1506_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745108271/50000000000 : ℝ) ≤ 4*Real.exp (8515/65536 : ℝ)*Real.exp (-mu (radius 8 (2129/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (102745108271/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2129/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1506_exp_radius
  have hrNumeric : (491944112453/500000000000 : ℝ) ≤ Real.exp (-2129/131072 : ℝ) ∧ Real.exp (-2129/131072 : ℝ) ≤ (983888224907/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491944112453/500000000000 : ℝ) ≤ (radius 8 (2129/16384 : ℝ)) ∧ (radius 8 (2129/16384 : ℝ)) ≤ (983888224907/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2129/16384 : ℝ)) (491944112453/500000000000 : ℝ) (983888224907/1000000000000 : ℝ) (35756935489/200000000000 : ℝ) (44696169363/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2129/16384 : ℝ)) (491944112453/500000000000 : ℝ) (983888224907/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2129/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491944112453/500000000000 : ℝ) (983888224907/1000000000000 : ℝ) (991944112453/1000000000000 : ℝ) (495972056227/500000000000 : ℝ) (39676455989/40000000000 : ℝ) (991911399727/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2129/16384 : ℝ)) 1 (991944112453/1000000000000 : ℝ) (495972056227/500000000000 : ℝ) (39676455989/40000000000 : ℝ) (991911399727/1000000000000 : ℝ) (991927756089/1000000000000 : ℝ) (991927756091/1000000000000 : ℝ) (495963877977/500000000000 : ℝ) (247981938989/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2129/16384 : ℝ)) 2 (991927756089/1000000000000 : ℝ) (991927756091/1000000000000 : ℝ) (495963877977/500000000000 : ℝ) (247981938989/250000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2129/16384 : ℝ)) 3 (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2129/16384 : ℝ)) 4 (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2129/16384 : ℝ)) 5 (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2129/16384 : ℝ)) 6 (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2129/16384 : ℝ)) 7 (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2129/16384 : ℝ))) (35756935489/200000000000 : ℝ) (44696169363/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2129/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35756935489/200000000000 : ℝ) (44696169363/250000000000 : ℝ) (294696169361/500000000000 : ℝ) (294696169363/500000000000 : ℝ) (422829371549/1000000000000 : ℝ) (211414685779/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2129/16384 : ℝ))) 1 (294696169361/500000000000 : ℝ) (294696169363/500000000000 : ℝ) (422829371549/1000000000000 : ℝ) (211414685779/500000000000 : ℝ) (101222171027/200000000000 : ℝ) (253055427571/500000000000 : ℝ) (62401471359/125000000000 : ℝ) (97502299/195312500 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2129/16384 : ℝ))) 2 (101222171027/200000000000 : ℝ) (253055427571/500000000000 : ℝ) (62401471359/125000000000 : ℝ) (97502299/195312500 : ℝ) (502661313003/1000000000000 : ℝ) (502661313011/1000000000000 : ℝ) (502649476523/1000000000000 : ℝ) (125662369133/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2129/16384 : ℝ))) 3 (502661313003/1000000000000 : ℝ) (502661313011/1000000000000 : ℝ) (502649476523/1000000000000 : ℝ) (125662369133/250000000000 : ℝ) (502655394763/1000000000000 : ℝ) (125663848693/250000000000 : ℝ) (62831924341/125000000000 : ℝ) (502655394737/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2129/16384 : ℝ))) 4 (502655394763/1000000000000 : ℝ) (125663848693/250000000000 : ℝ) (62831924341/125000000000 : ℝ) (502655394737/1000000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2129/16384 : ℝ))) 5 (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2129/16384 : ℝ))) 6 (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2129/16384 : ℝ))) 7 (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2129/16384 : ℝ)) hmem 8 (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2129/16384 : ℝ))) hcmem 8 (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2129/16384 : ℝ)) (991927756021/1000000000000 : ℝ) (123990969503/125000000000 : ℝ) (100531078949/200000000000 : ℝ) (100531078951/200000000000 : ℝ) (795994711221/1000000000000 : ℝ) (19899867781/25000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1506_exp_lower
  have heNumeric : (102745108271/50000000000 : ℝ)/4 ≤ Real.exp (-2131411591593/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745108271/50000000000 : ℝ)/4 ≤ Real.exp ((8515/65536 : ℝ)-(19899867781/25000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8515/65536 : ℝ) (2129/16384 : ℝ) (19899867781/25000000000 : ℝ) (102745108271/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1507; no trusted numerical premise.
theorem cover8_leaf1507_exp_radius : (31186607789299911/31250000000000000 : ℝ) ≤ Real.exp ((-8517/524288 : ℝ)/8) ∧ Real.exp ((-8517/524288 : ℝ)/8) ≤ (997971449257597153/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8517/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1507_exp_lower : (920113504145814191/1000000000000000000 : ℝ) ≤ Real.exp ((-2664263759279/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664263759279/4000000000000 : ℝ)/8) ≤ (57507094009113387/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664263759279/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1507_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902540549/1000000000000 : ℝ) ≤ 4*Real.exp (2129/16384 : ℝ)*Real.exp (-mu (radius 8 (8517/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902540549/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8517/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1507_exp_radius
  have hrNumeric : (98388634829/100000000000 : ℝ) ≤ Real.exp (-8517/524288 : ℝ) ∧ Real.exp (-8517/524288 : ℝ) ≤ (983886348291/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98388634829/100000000000 : ℝ) ≤ (radius 8 (8517/65536 : ℝ)) ∧ (radius 8 (8517/65536 : ℝ)) ≤ (983886348291/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8517/65536 : ℝ)) (98388634829/100000000000 : ℝ) (983886348291/1000000000000 : ℝ) (89397502267/500000000000 : ℝ) (178795004541/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8517/65536 : ℝ)) (98388634829/100000000000 : ℝ) (983886348291/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8517/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98388634829/100000000000 : ℝ) (983886348291/1000000000000 : ℝ) (198388634829/200000000000 : ℝ) (495971587073/500000000000 : ℝ) (198382090753/200000000000 : ℝ) (991910453767/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8517/65536 : ℝ)) 1 (198388634829/200000000000 : ℝ) (495971587073/500000000000 : ℝ) (198382090753/200000000000 : ℝ) (991910453767/1000000000000 : ℝ) (198385362791/200000000000 : ℝ) (991926813957/1000000000000 : ℝ) (49596340691/50000000000 : ℝ) (495963406911/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8517/65536 : ℝ)) 2 (198385362791/200000000000 : ℝ) (991926813957/1000000000000 : ℝ) (49596340691/50000000000 : ℝ) (495963406911/500000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8517/65536 : ℝ)) 3 (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8517/65536 : ℝ)) 4 (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8517/65536 : ℝ)) 5 (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8517/65536 : ℝ)) 6 (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8517/65536 : ℝ)) 7 (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8517/65536 : ℝ))) (89397502267/500000000000 : ℝ) (178795004541/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8517/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89397502267/500000000000 : ℝ) (178795004541/1000000000000 : ℝ) (589397502267/1000000000000 : ℝ) (589397502271/1000000000000 : ℝ) (21142079163/50000000000 : ℝ) (422841583269/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8517/65536 : ℝ))) 1 (589397502267/1000000000000 : ℝ) (589397502271/1000000000000 : ℝ) (21142079163/50000000000 : ℝ) (422841583269/1000000000000 : ℝ) (506119542763/1000000000000 : ℝ) (50611954277/100000000000 : ℝ) (249610583223/500000000000 : ℝ) (249610583227/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8517/65536 : ℝ))) 2 (506119542763/1000000000000 : ℝ) (50611954277/100000000000 : ℝ) (249610583223/500000000000 : ℝ) (249610583227/500000000000 : ℝ) (125667588651/250000000000 : ℝ) (125667588653/250000000000 : ℝ) (251329260383/500000000000 : ℝ) (20106340831/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8517/65536 : ℝ))) 3 (125667588651/250000000000 : ℝ) (125667588653/250000000000 : ℝ) (251329260383/500000000000 : ℝ) (20106340831/40000000000 : ℝ) (100532887537/200000000000 : ℝ) (251332218847/500000000000 : ℝ) (10053288753/20000000000 : ℝ) (502664437659/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8517/65536 : ℝ))) 4 (100532887537/200000000000 : ℝ) (251332218847/500000000000 : ℝ) (10053288753/20000000000 : ℝ) (502664437659/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8517/65536 : ℝ))) 5 (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8517/65536 : ℝ))) 6 (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8517/65536 : ℝ))) 7 (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8517/65536 : ℝ)) hmem 8 (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8517/65536 : ℝ))) hcmem 8 (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8517/65536 : ℝ)) (991926813887/1000000000000 : ℝ) (99192681389/100000000000 : ℝ) (502664437667/1000000000000 : ℝ) (502664437677/1000000000000 : ℝ) (796009787457/1000000000000 : ℝ) (199002446869/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1507_exp_lower
  have heNumeric : (2054902540549/1000000000000 : ℝ)/4 ≤ Real.exp (-2664263759279/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902540549/1000000000000 : ℝ)/4 ≤ Real.exp ((2129/16384 : ℝ)-(199002446869/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2129/16384 : ℝ) (8517/65536 : ℝ) (199002446869/250000000000 : ℝ) (2054902540549/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1508; no trusted numerical premise.
theorem cover8_leaf1508_exp_radius : (4989856056613453/5000000000000000 : ℝ) ≤ Real.exp ((-4259/262144 : ℝ)/8) ∧ Real.exp ((-4259/262144 : ℝ)/8) ≤ (997971211322690601/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4259/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1508_exp_lower : (92011352527967867/100000000000000000 : ℝ) ≤ Real.exp ((-2131410419423/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131410419423/3200000000000 : ℝ)/8) ≤ (920113525279678671/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131410419423/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1508_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902918137/1000000000000 : ℝ) ≤ 4*Real.exp (8517/65536 : ℝ)*Real.exp (-mu (radius 8 (4259/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902918137/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4259/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1508_exp_radius
  have hrNumeric : (983884471677/1000000000000 : ℝ) ≤ Real.exp (-4259/262144 : ℝ) ∧ Real.exp (-4259/262144 : ℝ) ≤ (491942235839/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983884471677/1000000000000 : ℝ) ≤ (radius 8 (4259/32768 : ℝ)) ∧ (radius 8 (4259/32768 : ℝ)) ≤ (491942235839/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4259/32768 : ℝ)) (983884471677/1000000000000 : ℝ) (491942235839/500000000000 : ℝ) (178805330991/1000000000000 : ℝ) (178805330997/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4259/32768 : ℝ)) (983884471677/1000000000000 : ℝ) (491942235839/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4259/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983884471677/1000000000000 : ℝ) (491942235839/500000000000 : ℝ) (495971117919/500000000000 : ℝ) (991942235839/1000000000000 : ℝ) (495954753903/500000000000 : ℝ) (30997172119/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4259/32768 : ℝ)) 1 (495971117919/500000000000 : ℝ) (991942235839/1000000000000 : ℝ) (495954753903/500000000000 : ℝ) (30997172119/31250000000 : ℝ) (495962935911/500000000000 : ℝ) (61995366989/62500000000 : ℝ) (991925871687/1000000000000 : ℝ) (991925871689/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4259/32768 : ℝ)) 2 (495962935911/500000000000 : ℝ) (61995366989/62500000000 : ℝ) (991925871687/1000000000000 : ℝ) (991925871689/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4259/32768 : ℝ)) 3 (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4259/32768 : ℝ)) 4 (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4259/32768 : ℝ)) 5 (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4259/32768 : ℝ)) 6 (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4259/32768 : ℝ)) 7 (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4259/32768 : ℝ))) (178805330991/1000000000000 : ℝ) (178805330997/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4259/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178805330991/1000000000000 : ℝ) (178805330997/1000000000000 : ℝ) (117880533099/200000000000 : ℝ) (589402665499/1000000000000 : ℝ) (42285379387/100000000000 : ℝ) (211426896939/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4259/32768 : ℝ))) 1 (117880533099/200000000000 : ℝ) (589402665499/1000000000000 : ℝ) (42285379387/100000000000 : ℝ) (211426896939/500000000000 : ℝ) (253064114841/500000000000 : ℝ) (506128229689/1000000000000 : ℝ) (99846112237/200000000000 : ℝ) (62403820149/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4259/32768 : ℝ))) 2 (253064114841/500000000000 : ℝ) (506128229689/1000000000000 : ℝ) (99846112237/200000000000 : ℝ) (62403820149/125000000000 : ℝ) (502679395433/1000000000000 : ℝ) (502679395441/1000000000000 : ℝ) (125666891059/250000000000 : ℝ) (125666891061/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4259/32768 : ℝ))) 3 (502679395433/1000000000000 : ℝ) (502679395441/1000000000000 : ℝ) (125666891059/250000000000 : ℝ) (125666891061/250000000000 : ℝ) (251336739917/500000000000 : ℝ) (502673479843/1000000000000 : ℝ) (502673479799/1000000000000 : ℝ) (3927136561/7812500000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4259/32768 : ℝ))) 4 (251336739917/500000000000 : ℝ) (502673479843/1000000000000 : ℝ) (502673479799/1000000000000 : ℝ) (3927136561/7812500000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4259/32768 : ℝ))) 5 (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4259/32768 : ℝ))) 6 (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4259/32768 : ℝ))) 7 (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4259/32768 : ℝ)) hmem 8 (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4259/32768 : ℝ))) hcmem 8 (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4259/32768 : ℝ)) (495962935877/500000000000 : ℝ) (991925871757/1000000000000 : ℝ) (62834184977/125000000000 : ℝ) (251336739913/500000000000 : ℝ) (24875776953/31250000000 : ℝ) (159204972503/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1508_exp_lower
  have heNumeric : (2054902918137/1000000000000 : ℝ)/4 ≤ Real.exp (-2131410419423/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902918137/1000000000000 : ℝ)/4 ≤ Real.exp ((8517/65536 : ℝ)-(159204972503/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8517/65536 : ℝ) (4259/32768 : ℝ) (159204972503/200000000000 : ℝ) (2054902918137/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1509; no trusted numerical premise.
theorem cover8_leaf1509_exp_radius : (997970973387840777/1000000000000000000 : ℝ) ≤ Real.exp ((-8519/524288 : ℝ)/8) ∧ Real.exp ((-8519/524288 : ℝ)/8) ≤ (498985486693920389/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8519/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1509_exp_lower : (920113546551560667/1000000000000000000 : ℝ) ≤ Real.exp ((-5328524568957/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328524568957/8000000000000 : ℝ)/8) ≤ (230028386637890167/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328524568957/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1509_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431456137/62500000000 : ℝ) ≤ 4*Real.exp (4259/32768 : ℝ)*Real.exp (-mu (radius 8 (8519/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (128431456137/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8519/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1509_exp_radius
  have hrNumeric : (245970648767/250000000000 : ℝ) ≤ Real.exp (-8519/524288 : ℝ) ∧ Real.exp (-8519/524288 : ℝ) ≤ (983882595069/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245970648767/250000000000 : ℝ) ≤ (radius 8 (8519/65536 : ℝ)) ∧ (radius 8 (8519/65536 : ℝ)) ≤ (983882595069/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8519/65536 : ℝ)) (245970648767/250000000000 : ℝ) (983882595069/1000000000000 : ℝ) (178815656809/1000000000000 : ℝ) (11175978551/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8519/65536 : ℝ)) (245970648767/250000000000 : ℝ) (983882595069/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8519/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245970648767/250000000000 : ℝ) (983882595069/1000000000000 : ℝ) (495970648767/500000000000 : ℝ) (198388259507/200000000000 : ℝ) (123988570231/125000000000 : ℝ) (991908561849/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8519/65536 : ℝ)) 1 (495970648767/500000000000 : ℝ) (198388259507/200000000000 : ℝ) (123988570231/125000000000 : ℝ) (991908561849/1000000000000 : ℝ) (991924929691/1000000000000 : ℝ) (247981232423/250000000000 : ℝ) (198384985911/200000000000 : ℝ) (991924929557/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8519/65536 : ℝ)) 2 (991924929691/1000000000000 : ℝ) (247981232423/250000000000 : ℝ) (198384985911/200000000000 : ℝ) (991924929557/1000000000000 : ℝ) (991924929623/1000000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8519/65536 : ℝ)) 3 (991924929623/1000000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8519/65536 : ℝ)) 4 (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8519/65536 : ℝ)) 5 (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8519/65536 : ℝ)) 6 (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8519/65536 : ℝ)) 7 (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8519/65536 : ℝ))) (178815656809/1000000000000 : ℝ) (11175978551/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8519/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178815656809/1000000000000 : ℝ) (11175978551/62500000000 : ℝ) (147351957101/250000000000 : ℝ) (73675978551/125000000000 : ℝ) (422866003373/1000000000000 : ℝ) (211433001691/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8519/65536 : ℝ))) 1 (147351957101/250000000000 : ℝ) (73675978551/125000000000 : ℝ) (422866003373/1000000000000 : ℝ) (211433001691/500000000000 : ℝ) (31633557243/62500000000 : ℝ) (101227383179/200000000000 : ℝ) (99847991017/200000000000 : ℝ) (499239955093/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8519/65536 : ℝ))) 2 (31633557243/62500000000 : ℝ) (101227383179/200000000000 : ℝ) (99847991017/200000000000 : ℝ) (499239955093/1000000000000 : ℝ) (251344217743/500000000000 : ℝ) (251344217747/500000000000 : ℝ) (50267660693/100000000000 : ℝ) (251338303469/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8519/65536 : ℝ))) 3 (251344217743/500000000000 : ℝ) (251344217747/500000000000 : ℝ) (50267660693/100000000000 : ℝ) (251338303469/500000000000 : ℝ) (62835315151/125000000000 : ℝ) (3927207197/7812500000 : ℝ) (502682521173/1000000000000 : ℝ) (251341260591/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8519/65536 : ℝ))) 4 (62835315151/125000000000 : ℝ) (3927207197/7812500000 : ℝ) (502682521173/1000000000000 : ℝ) (251341260591/500000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8519/65536 : ℝ))) 5 (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8519/65536 : ℝ))) 6 (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8519/65536 : ℝ))) 7 (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8519/65536 : ℝ)) hmem 8 (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8519/65536 : ℝ))) hcmem 8 (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8519/65536 : ℝ)) (495962464811/500000000000 : ℝ) (7935399437/8000000000 : ℝ) (50268252119/100000000000 : ℝ) (502682521199/1000000000000 : ℝ) (49752496021/62500000000 : ℝ) (398019968177/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1509_exp_lower
  have heNumeric : (128431456137/62500000000 : ℝ)/4 ≤ Real.exp (-5328524568957/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431456137/62500000000 : ℝ)/4 ≤ Real.exp ((4259/32768 : ℝ)-(398019968177/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4259/32768 : ℝ) (8519/65536 : ℝ) (398019968177/500000000000 : ℝ) (128431456137/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1510; no trusted numerical premise.
theorem cover8_leaf1510_exp_radius : (997970735453047681/1000000000000000000 : ℝ) ≤ Real.exp ((-1065/65536 : ℝ)/8) ∧ Real.exp ((-1065/65536 : ℝ)/8) ≤ (498985367726523841/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1510_exp_lower : (460056783980902617/500000000000000000 : ℝ) ≤ Real.exp ((-2131409231893/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131409231893/3200000000000 : ℝ)/8) ≤ (184022713592361047/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131409231893/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1510_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451840359/500000000000 : ℝ) ≤ 4*Real.exp (8519/65536 : ℝ)*Real.exp (-mu (radius 8 (1065/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451840359/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1065/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1510_exp_radius
  have hrNumeric : (983880718463/1000000000000 : ℝ) ≤ Real.exp (-1065/65536 : ℝ) ∧ Real.exp (-1065/65536 : ℝ) ≤ (7686568113/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983880718463/1000000000000 : ℝ) ≤ (radius 8 (1065/8192 : ℝ)) ∧ (radius 8 (1065/8192 : ℝ)) ≤ (7686568113/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1065/8192 : ℝ)) (983880718463/1000000000000 : ℝ) (7686568113/7812500000 : ℝ) (17882598199/100000000000 : ℝ) (44706495499/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1065/8192 : ℝ)) (983880718463/1000000000000 : ℝ) (7686568113/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1065/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983880718463/1000000000000 : ℝ) (7686568113/7812500000 : ℝ) (991940359231/1000000000000 : ℝ) (15499068113/15625000000 : ℝ) (991907615891/1000000000000 : ℝ) (247976903973/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1065/8192 : ℝ)) 1 (991940359231/1000000000000 : ℝ) (15499068113/15625000000 : ℝ) (991907615891/1000000000000 : ℝ) (247976903973/250000000000 : ℝ) (991923987561/1000000000000 : ℝ) (495961993781/500000000000 : ℝ) (39676959497/40000000000 : ℝ) (991923987427/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1065/8192 : ℝ)) 2 (991923987561/1000000000000 : ℝ) (495961993781/500000000000 : ℝ) (39676959497/40000000000 : ℝ) (991923987427/1000000000000 : ℝ) (991923987493/1000000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1065/8192 : ℝ)) 3 (991923987493/1000000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1065/8192 : ℝ)) 4 (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1065/8192 : ℝ)) 5 (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1065/8192 : ℝ)) 6 (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1065/8192 : ℝ)) 7 (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1065/8192 : ℝ))) (17882598199/100000000000 : ℝ) (44706495499/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1065/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17882598199/100000000000 : ℝ) (44706495499/250000000000 : ℝ) (117882598199/200000000000 : ℝ) (294706495499/500000000000 : ℝ) (42287821177/100000000000 : ℝ) (211439105889/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1065/8192 : ℝ))) 1 (117882598199/200000000000 : ℝ) (294706495499/500000000000 : ℝ) (42287821177/100000000000 : ℝ) (211439105889/500000000000 : ℝ) (253072800691/500000000000 : ℝ) (126536400347/250000000000 : ℝ) (499249348147/1000000000000 : ℝ) (249624674077/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1065/8192 : ℝ))) 2 (253072800691/500000000000 : ℝ) (126536400347/250000000000 : ℝ) (499249348147/1000000000000 : ℝ) (249624674077/500000000000 : ℝ) (125674368691/250000000000 : ℝ) (502697474771/1000000000000 : ℝ) (502685648847/1000000000000 : ℝ) (100537129771/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1065/8192 : ℝ))) 3 (125674368691/250000000000 : ℝ) (502697474771/1000000000000 : ℝ) (502685648847/1000000000000 : ℝ) (100537129771/200000000000 : ℝ) (100538312361/200000000000 : ℝ) (502691561813/1000000000000 : ℝ) (50269156177/100000000000 : ℝ) (502691561779/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1065/8192 : ℝ))) 4 (100538312361/200000000000 : ℝ) (502691561813/1000000000000 : ℝ) (50269156177/100000000000 : ℝ) (502691561779/1000000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1065/8192 : ℝ))) 5 (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1065/8192 : ℝ))) 6 (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1065/8192 : ℝ))) 7 (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1065/8192 : ℝ)) hmem 8 (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1065/8192 : ℝ))) hcmem 8 (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1065/8192 : ℝ)) (247980996873/250000000000 : ℝ) (198384797499/200000000000 : ℝ) (502691561787/1000000000000 : ℝ) (125672890449/250000000000 : ℝ) (199013752243/250000000000 : ℝ) (79605500899/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1510_exp_lower
  have heNumeric : (1027451840359/500000000000 : ℝ)/4 ≤ Real.exp (-2131409231893/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451840359/500000000000 : ℝ)/4 ≤ Real.exp ((8519/65536 : ℝ)-(79605500899/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8519/65536 : ℝ) (1065/8192 : ℝ) (79605500899/100000000000 : ℝ) (1027451840359/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1511; no trusted numerical premise.
theorem cover8_leaf1511_exp_radius : (997970497518311313/1000000000000000000 : ℝ) ≤ Real.exp ((-8521/524288 : ℝ)/8) ∧ Real.exp ((-8521/524288 : ℝ)/8) ≤ (498985248759155657/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8521/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1511_exp_lower : (920113589509262237/1000000000000000000 : ℝ) ≤ Real.exp ((-1332130395241/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332130395241/2000000000000 : ℝ)/8) ≤ (460056794754631119/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332130395241/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1511_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904065697/1000000000000 : ℝ) ≤ 4*Real.exp (1065/8192 : ℝ)*Real.exp (-mu (radius 8 (8521/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904065697/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8521/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1511_exp_radius
  have hrNumeric : (983878841861/1000000000000 : ℝ) ≤ Real.exp (-8521/524288 : ℝ) ∧ Real.exp (-8521/524288 : ℝ) ≤ (491939420931/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983878841861/1000000000000 : ℝ) ≤ (radius 8 (8521/65536 : ℝ)) ∧ (radius 8 (8521/65536 : ℝ)) ≤ (491939420931/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8521/65536 : ℝ)) (983878841861/1000000000000 : ℝ) (491939420931/500000000000 : ℝ) (89418153269/500000000000 : ℝ) (11177269159/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8521/65536 : ℝ)) (983878841861/1000000000000 : ℝ) (491939420931/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8521/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983878841861/1000000000000 : ℝ) (491939420931/500000000000 : ℝ) (99193942093/100000000000 : ℝ) (991939420931/1000000000000 : ℝ) (495953334967/500000000000 : ℝ) (61994166871/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8521/65536 : ℝ)) 1 (99193942093/100000000000 : ℝ) (991939420931/1000000000000 : ℝ) (495953334967/500000000000 : ℝ) (61994166871/62500000000 : ℝ) (123990380679/125000000000 : ℝ) (495961522717/500000000000 : ℝ) (61995190331/62500000000 : ℝ) (991923045299/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8521/65536 : ℝ)) 2 (123990380679/125000000000 : ℝ) (495961522717/500000000000 : ℝ) (61995190331/62500000000 : ℝ) (991923045299/1000000000000 : ℝ) (247980761341/250000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8521/65536 : ℝ)) 3 (247980761341/250000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8521/65536 : ℝ)) 4 (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8521/65536 : ℝ)) 5 (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8521/65536 : ℝ)) 6 (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8521/65536 : ℝ)) 7 (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8521/65536 : ℝ))) (89418153269/500000000000 : ℝ) (11177269159/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8521/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89418153269/500000000000 : ℝ) (11177269159/62500000000 : ℝ) (589418153269/1000000000000 : ℝ) (73677269159/125000000000 : ℝ) (211445209533/500000000000 : ℝ) (211445209537/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8521/65536 : ℝ))) 1 (589418153269/1000000000000 : ℝ) (73677269159/125000000000 : ℝ) (211445209533/500000000000 : ℝ) (211445209537/500000000000 : ℝ) (506154286167/1000000000000 : ℝ) (506154286173/1000000000000 : ℝ) (3994069923/8000000000 : ℝ) (249629370191/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8521/65536 : ℝ))) 2 (506154286167/1000000000000 : ℝ) (506154286173/1000000000000 : ℝ) (3994069923/8000000000 : ℝ) (249629370191/500000000000 : ℝ) (502706513271/1000000000000 : ℝ) (251353256639/500000000000 : ℝ) (62836836249/125000000000 : ℝ) (50269469/100000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8521/65536 : ℝ))) 3 (502706513271/1000000000000 : ℝ) (251353256639/500000000000 : ℝ) (62836836249/125000000000 : ℝ) (50269469/100000000 : ℝ) (502700601631/1000000000000 : ℝ) (502700601639/1000000000000 : ℝ) (125675150399/250000000000 : ℝ) (100540120321/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8521/65536 : ℝ))) 4 (502700601631/1000000000000 : ℝ) (502700601639/1000000000000 : ℝ) (125675150399/250000000000 : ℝ) (100540120321/200000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8521/65536 : ℝ))) 5 (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8521/65536 : ℝ))) 6 (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8521/65536 : ℝ))) 7 (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8521/65536 : ℝ)) hmem 8 (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8521/65536 : ℝ))) hcmem 8 (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8521/65536 : ℝ)) (991923045363/1000000000000 : ℝ) (991923045367/1000000000000 : ℝ) (502700601613/1000000000000 : ℝ) (251350300811/500000000000 : ℝ) (159214016083/200000000000 : ℝ) (796070080433/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1511_exp_lower
  have heNumeric : (2054904065697/1000000000000 : ℝ)/4 ≤ Real.exp (-1332130395241/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904065697/1000000000000 : ℝ)/4 ≤ Real.exp ((1065/8192 : ℝ)-(796070080433/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1065/8192 : ℝ) (8521/65536 : ℝ) (796070080433/1000000000000 : ℝ) (2054904065697/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1512; no trusted numerical premise.
theorem cover8_leaf1512_exp_radius : (498985129791815837/500000000000000000 : ℝ) ≤ Real.exp ((-4261/262144 : ℝ)/8) ∧ Real.exp ((-4261/262144 : ℝ)/8) ≤ (39918810383345267/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4261/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1512_exp_lower : (920113611194851801/1000000000000000000 : ℝ) ≤ Real.exp ((-426281605807/640000000000 : ℝ)/8) ∧ Real.exp ((-426281605807/640000000000 : ℝ)/8) ≤ (460056805597425901/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-426281605807/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1512_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904453143/1000000000000 : ℝ) ≤ 4*Real.exp (8521/65536 : ℝ)*Real.exp (-mu (radius 8 (4261/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904453143/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4261/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1512_exp_radius
  have hrNumeric : (983876965263/1000000000000 : ℝ) ≤ Real.exp (-4261/262144 : ℝ) ∧ Real.exp (-4261/262144 : ℝ) ≤ (61492310329/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983876965263/1000000000000 : ℝ) ≤ (radius 8 (4261/32768 : ℝ)) ∧ (radius 8 (4261/32768 : ℝ)) ≤ (61492310329/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4261/32768 : ℝ)) (983876965263/1000000000000 : ℝ) (61492310329/62500000000 : ℝ) (11177914403/62500000000 : ℝ) (35769326091/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4261/32768 : ℝ)) (983876965263/1000000000000 : ℝ) (61492310329/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4261/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983876965263/1000000000000 : ℝ) (61492310329/62500000000 : ℝ) (991938482631/1000000000000 : ℝ) (123992310329/125000000000 : ℝ) (991905723979/1000000000000 : ℝ) (49595286199/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4261/32768 : ℝ)) 1 (991938482631/1000000000000 : ℝ) (123992310329/125000000000 : ℝ) (991905723979/1000000000000 : ℝ) (49595286199/50000000000 : ℝ) (198384420661/200000000000 : ℝ) (495961051653/500000000000 : ℝ) (991922103169/1000000000000 : ℝ) (991922103171/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4261/32768 : ℝ)) 2 (198384420661/200000000000 : ℝ) (495961051653/500000000000 : ℝ) (991922103169/1000000000000 : ℝ) (991922103171/1000000000000 : ℝ) (991922103237/1000000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4261/32768 : ℝ)) 3 (991922103237/1000000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4261/32768 : ℝ)) 4 (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4261/32768 : ℝ)) 5 (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4261/32768 : ℝ)) 6 (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4261/32768 : ℝ)) 7 (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4261/32768 : ℝ))) (11177914403/62500000000 : ℝ) (35769326091/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4261/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11177914403/62500000000 : ℝ) (35769326091/200000000000 : ℝ) (73677914403/125000000000 : ℝ) (147355828807/250000000000 : ℝ) (84580525051/200000000000 : ℝ) (26431414079/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4261/32768 : ℝ))) 1 (73677914403/125000000000 : ℝ) (147355828807/250000000000 : ℝ) (84580525051/200000000000 : ℝ) (26431414079/62500000000 : ℝ) (506162970239/1000000000000 : ℝ) (253081485123/500000000000 : ℝ) (499268131763/1000000000000 : ℝ) (499268131771/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4261/32768 : ℝ))) 2 (506162970239/1000000000000 : ℝ) (253081485123/500000000000 : ℝ) (499268131763/1000000000000 : ℝ) (499268131771/1000000000000 : ℝ) (502715551001/1000000000000 : ℝ) (502715551009/1000000000000 : ℝ) (12567593259/25000000000 : ℝ) (502703730369/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4261/32768 : ℝ))) 3 (502715551001/1000000000000 : ℝ) (502715551009/1000000000000 : ℝ) (12567593259/25000000000 : ℝ) (502703730369/1000000000000 : ℝ) (12567741017/25000000000 : ℝ) (502709640689/1000000000000 : ℝ) (100541928129/200000000000 : ℝ) (100541928131/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4261/32768 : ℝ))) 4 (12567741017/25000000000 : ℝ) (502709640689/1000000000000 : ℝ) (100541928129/200000000000 : ℝ) (100541928131/200000000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4261/32768 : ℝ))) 5 (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4261/32768 : ℝ))) 6 (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4261/32768 : ℝ))) 7 (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4261/32768 : ℝ)) hmem 8 (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4261/32768 : ℝ))) hcmem 8 (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4261/32768 : ℝ)) (247980525809/250000000000 : ℝ) (991922103239/1000000000000 : ℝ) (251354820331/500000000000 : ℝ) (15709676271/31250000000 : ℝ) (12438830479/15625000000 : ℝ) (31843406027/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1512_exp_lower
  have heNumeric : (2054904453143/1000000000000 : ℝ)/4 ≤ Real.exp (-426281605807/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904453143/1000000000000 : ℝ)/4 ≤ Real.exp ((8521/65536 : ℝ)-(31843406027/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8521/65536 : ℝ) (4261/32768 : ℝ) (31843406027/40000000000 : ℝ) (2054904453143/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1513; no trusted numerical premise.
theorem cover8_leaf1513_exp_radius : (498985010824504381/500000000000000000 : ℝ) ≤ Real.exp ((-8523/524288 : ℝ)/8) ∧ Real.exp ((-8523/524288 : ℝ)/8) ≤ (997970021649008763/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8523/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1513_exp_lower : (230028408254442209/250000000000000000 : ℝ) ≤ Real.exp ((-5328518554659/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328518554659/8000000000000 : ℝ)/8) ≤ (920113633017768837/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328518554659/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1513_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452421521/500000000000 : ℝ) ≤ 4*Real.exp (4261/32768 : ℝ)*Real.exp (-mu (radius 8 (8523/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452421521/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8523/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1513_exp_radius
  have hrNumeric : (245968772167/250000000000 : ℝ) ≤ Real.exp (-8523/524288 : ℝ) ∧ Real.exp (-8523/524288 : ℝ) ≤ (983875088669/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245968772167/250000000000 : ℝ) ≤ (radius 8 (8523/65536 : ℝ)) ∧ (radius 8 (8523/65536 : ℝ)) ≤ (983875088669/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8523/65536 : ℝ)) (245968772167/250000000000 : ℝ) (983875088669/1000000000000 : ℝ) (178856953727/1000000000000 : ℝ) (178856953733/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8523/65536 : ℝ)) (245968772167/250000000000 : ℝ) (983875088669/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8523/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245968772167/250000000000 : ℝ) (983875088669/1000000000000 : ℝ) (495968772167/500000000000 : ℝ) (198387508867/200000000000 : ℝ) (123988097253/125000000000 : ℝ) (495952389013/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8523/65536 : ℝ)) 1 (495968772167/500000000000 : ℝ) (198387508867/200000000000 : ℝ) (123988097253/125000000000 : ℝ) (495952389013/500000000000 : ℝ) (991921161179/1000000000000 : ℝ) (991921161181/1000000000000 : ℝ) (991921161043/1000000000000 : ℝ) (495960580523/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8523/65536 : ℝ)) 2 (991921161179/1000000000000 : ℝ) (991921161181/1000000000000 : ℝ) (991921161043/1000000000000 : ℝ) (495960580523/500000000000 : ℝ) (991921161111/1000000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8523/65536 : ℝ)) 3 (991921161111/1000000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8523/65536 : ℝ)) 4 (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8523/65536 : ℝ)) 5 (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8523/65536 : ℝ)) 6 (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8523/65536 : ℝ)) 7 (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8523/65536 : ℝ))) (178856953727/1000000000000 : ℝ) (178856953733/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8523/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178856953727/1000000000000 : ℝ) (178856953733/1000000000000 : ℝ) (589428476863/1000000000000 : ℝ) (589428476867/1000000000000 : ℝ) (211457415173/500000000000 : ℝ) (211457415177/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8523/65536 : ℝ))) 1 (589428476863/1000000000000 : ℝ) (589428476867/1000000000000 : ℝ) (211457415173/500000000000 : ℝ) (211457415177/500000000000 : ℝ) (126542913401/250000000000 : ℝ) (506171653611/1000000000000 : ℝ) (499277522319/1000000000000 : ℝ) (499277522327/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8523/65536 : ℝ))) 2 (126542913401/250000000000 : ℝ) (506171653611/1000000000000 : ℝ) (499277522319/1000000000000 : ℝ) (499277522327/1000000000000 : ℝ) (502724587961/1000000000000 : ℝ) (502724587969/1000000000000 : ℝ) (251356384979/500000000000 : ℝ) (502712769967/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8523/65536 : ℝ))) 3 (502724587961/1000000000000 : ℝ) (502724587969/1000000000000 : ℝ) (251356384979/500000000000 : ℝ) (502712769967/1000000000000 : ℝ) (502718678959/1000000000000 : ℝ) (62839834871/125000000000 : ℝ) (125679669731/250000000000 : ℝ) (251359339467/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8523/65536 : ℝ))) 4 (502718678959/1000000000000 : ℝ) (62839834871/125000000000 : ℝ) (125679669731/250000000000 : ℝ) (251359339467/500000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8523/65536 : ℝ))) 5 (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8523/65536 : ℝ))) 6 (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8523/65536 : ℝ))) 7 (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8523/65536 : ℝ)) hmem 8 (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8523/65536 : ℝ))) hcmem 8 (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8523/65536 : ℝ)) (99192116111/100000000000 : ℝ) (495960580557/500000000000 : ℝ) (502718678941/1000000000000 : ℝ) (502718678951/1000000000000 : ℝ) (796100219703/1000000000000 : ℝ) (796100219723/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1513_exp_lower
  have heNumeric : (1027452421521/500000000000 : ℝ)/4 ≤ Real.exp (-5328518554659/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452421521/500000000000 : ℝ)/4 ≤ Real.exp ((4261/32768 : ℝ)-(796100219723/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4261/32768 : ℝ) (8523/65536 : ℝ) (796100219723/1000000000000 : ℝ) (1027452421521/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1514; no trusted numerical premise.
theorem cover8_leaf1514_exp_radius : (997969783714442579/1000000000000000000 : ℝ) ≤ Real.exp ((-2131/131072 : ℝ)/8) ∧ Real.exp ((-2131/131072 : ℝ)/8) ≤ (49898489185722129/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1514_exp_lower : (920113654978703437/1000000000000000000 : ℝ) ≤ Real.exp ((-10657034054261/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657034054261/16000000000000 : ℝ)/8) ≤ (460056827489351719/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657034054261/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1514_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431577213/62500000000 : ℝ) ≤ 4*Real.exp (8523/65536 : ℝ)*Real.exp (-mu (radius 8 (2131/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (128431577213/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2131/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1514_exp_radius
  have hrNumeric : (983873212077/1000000000000 : ℝ) ≤ Real.exp (-2131/131072 : ℝ) ∧ Real.exp (-2131/131072 : ℝ) ≤ (491936606039/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983873212077/1000000000000 : ℝ) ≤ (radius 8 (2131/16384 : ℝ)) ∧ (radius 8 (2131/16384 : ℝ)) ≤ (491936606039/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2131/16384 : ℝ)) (983873212077/1000000000000 : ℝ) (491936606039/500000000000 : ℝ) (11179204773/62500000000 : ℝ) (89433638187/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2131/16384 : ℝ)) (983873212077/1000000000000 : ℝ) (491936606039/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2131/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983873212077/1000000000000 : ℝ) (491936606039/500000000000 : ℝ) (495968303019/500000000000 : ℝ) (991936606039/1000000000000 : ℝ) (99190383207/100000000000 : ℝ) (123987979009/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2131/16384 : ℝ)) 1 (495968303019/500000000000 : ℝ) (991936606039/1000000000000 : ℝ) (99190383207/100000000000 : ℝ) (123987979009/125000000000 : ℝ) (495960109527/500000000000 : ℝ) (61995013691/62500000000 : ℝ) (495960109459/500000000000 : ℝ) (991920218921/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2131/16384 : ℝ)) 2 (495960109527/500000000000 : ℝ) (61995013691/62500000000 : ℝ) (495960109459/500000000000 : ℝ) (991920218921/1000000000000 : ℝ) (495960109493/500000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2131/16384 : ℝ)) 3 (495960109493/500000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2131/16384 : ℝ)) 4 (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2131/16384 : ℝ)) 5 (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2131/16384 : ℝ)) 6 (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2131/16384 : ℝ)) 7 (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2131/16384 : ℝ))) (11179204773/62500000000 : ℝ) (89433638187/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2131/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11179204773/62500000000 : ℝ) (89433638187/500000000000 : ℝ) (73679204773/125000000000 : ℝ) (589433638187/1000000000000 : ℝ) (42292703433/100000000000 : ℝ) (422927034339/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2131/16384 : ℝ))) 1 (73679204773/125000000000 : ℝ) (589433638187/1000000000000 : ℝ) (42292703433/100000000000 : ℝ) (422927034339/1000000000000 : ℝ) (506180336257/1000000000000 : ℝ) (506180336263/1000000000000 : ℝ) (499286912037/1000000000000 : ℝ) (124821728011/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2131/16384 : ℝ))) 2 (506180336257/1000000000000 : ℝ) (506180336263/1000000000000 : ℝ) (499286912037/1000000000000 : ℝ) (124821728011/250000000000 : ℝ) (502733624147/1000000000000 : ℝ) (251366812077/500000000000 : ℝ) (25136090439/50000000000 : ℝ) (125680452197/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2131/16384 : ℝ))) 3 (502733624147/1000000000000 : ℝ) (251366812077/500000000000 : ℝ) (25136090439/50000000000 : ℝ) (125680452197/250000000000 : ℝ) (502727716463/1000000000000 : ℝ) (502727716471/1000000000000 : ℝ) (125681929107/250000000000 : ℝ) (502727716437/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2131/16384 : ℝ))) 4 (502727716463/1000000000000 : ℝ) (502727716471/1000000000000 : ℝ) (125681929107/250000000000 : ℝ) (502727716437/1000000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2131/16384 : ℝ))) 5 (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2131/16384 : ℝ))) 6 (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2131/16384 : ℝ))) 7 (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2131/16384 : ℝ)) hmem 8 (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2131/16384 : ℝ))) hcmem 8 (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2131/16384 : ℝ)) (198384043797/200000000000 : ℝ) (991920218989/1000000000000 : ℝ) (100545543289/200000000000 : ℝ) (251363858227/500000000000 : ℝ) (1554912671/1953125000 : ℝ) (796115287571/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1514_exp_lower
  have heNumeric : (128431577213/62500000000 : ℝ)/4 ≤ Real.exp (-10657034054261/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431577213/62500000000 : ℝ)/4 ≤ Real.exp ((8523/65536 : ℝ)-(796115287571/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8523/65536 : ℝ) (2131/16384 : ℝ) (796115287571/1000000000000 : ℝ) (128431577213/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1515; no trusted numerical premise.
theorem cover8_leaf1515_exp_radius : (997969545779933123/1000000000000000000 : ℝ) ≤ Real.exp ((-8525/524288 : ℝ)/8) ∧ Real.exp ((-8525/524288 : ℝ)/8) ≤ (249492386444983281/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1515_exp_lower : (460056838538942821/500000000000000000 : ℝ) ≤ Real.exp ((-2664257744993/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664257744993/4000000000000 : ℝ)/8) ≤ (920113677077885643/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664257744993/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1515_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726407561/250000000000 : ℝ) ≤ 4*Real.exp (2131/16384 : ℝ)*Real.exp (-mu (radius 8 (8525/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513726407561/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8525/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1515_exp_radius
  have hrNumeric : (98387133549/100000000000 : ℝ) ≤ Real.exp (-8525/524288 : ℝ) ∧ Real.exp (-8525/524288 : ℝ) ≤ (983871335491/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98387133549/100000000000 : ℝ) ≤ (radius 8 (8525/65536 : ℝ)) ∧ (radius 8 (8525/65536 : ℝ)) ≤ (983871335491/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8525/65536 : ℝ)) (98387133549/100000000000 : ℝ) (983871335491/1000000000000 : ℝ) (178877598371/1000000000000 : ℝ) (89438799189/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8525/65536 : ℝ)) (98387133549/100000000000 : ℝ) (983871335491/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8525/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98387133549/100000000000 : ℝ) (983871335491/1000000000000 : ℝ) (198387133549/200000000000 : ℝ) (495967833873/500000000000 : ℝ) (495951443059/500000000000 : ℝ) (991902886119/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8525/65536 : ℝ)) 1 (198387133549/200000000000 : ℝ) (495967833873/500000000000 : ℝ) (495951443059/500000000000 : ℝ) (991902886119/1000000000000 : ℝ) (991919276931/1000000000000 : ℝ) (991919276933/1000000000000 : ℝ) (247979819199/250000000000 : ℝ) (495959638399/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8525/65536 : ℝ)) 2 (991919276931/1000000000000 : ℝ) (991919276933/1000000000000 : ℝ) (247979819199/250000000000 : ℝ) (495959638399/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8525/65536 : ℝ)) 3 (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8525/65536 : ℝ)) 4 (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8525/65536 : ℝ)) 5 (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8525/65536 : ℝ)) 6 (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8525/65536 : ℝ)) 7 (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8525/65536 : ℝ))) (178877598371/1000000000000 : ℝ) (89438799189/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8525/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178877598371/1000000000000 : ℝ) (89438799189/500000000000 : ℝ) (117887759837/200000000000 : ℝ) (589438799189/1000000000000 : ℝ) (422939237209/1000000000000 : ℝ) (211469618609/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8525/65536 : ℝ))) 1 (117887759837/200000000000 : ℝ) (589438799189/1000000000000 : ℝ) (422939237209/1000000000000 : ℝ) (211469618609/500000000000 : ℝ) (506189018197/1000000000000 : ℝ) (126547254551/250000000000 : ℝ) (124824075229/250000000000 : ℝ) (124824075231/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8525/65536 : ℝ))) 2 (506189018197/1000000000000 : ℝ) (126547254551/250000000000 : ℝ) (124824075229/250000000000 : ℝ) (124824075231/250000000000 : ℝ) (125685664889/250000000000 : ℝ) (125685664891/250000000000 : ℝ) (20109233873/40000000000 : ℝ) (251365423417/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8525/65536 : ℝ))) 3 (125685664889/250000000000 : ℝ) (125685664891/250000000000 : ℝ) (20109233873/40000000000 : ℝ) (251365423417/500000000000 : ℝ) (50273675319/100000000000 : ℝ) (502736753199/1000000000000 : ℝ) (100547350631/200000000000 : ℝ) (100547350633/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8525/65536 : ℝ))) 4 (50273675319/100000000000 : ℝ) (502736753199/1000000000000 : ℝ) (100547350631/200000000000 : ℝ) (100547350633/200000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8525/65536 : ℝ))) 5 (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8525/65536 : ℝ))) 6 (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8525/65536 : ℝ))) 7 (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8525/65536 : ℝ)) hmem 8 (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8525/65536 : ℝ))) hcmem 8 (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8525/65536 : ℝ)) (991919276863/1000000000000 : ℝ) (495959638433/500000000000 : ℝ) (125684188293/250000000000 : ℝ) (251368376591/500000000000 : ℝ) (398065177099/500000000000 : ℝ) (796130354217/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1515_exp_lower
  have heNumeric : (513726407561/250000000000 : ℝ)/4 ≤ Real.exp (-2664257744993/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726407561/250000000000 : ℝ)/4 ≤ Real.exp ((2131/16384 : ℝ)-(796130354217/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2131/16384 : ℝ) (8525/65536 : ℝ) (796130354217/1000000000000 : ℝ) (513726407561/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1516; no trusted numerical premise.
theorem cover8_leaf1516_exp_radius : (249492326961370099/250000000000000000 : ℝ) ≤ Real.exp ((-4263/262144 : ℝ)/8) ∧ Real.exp ((-4263/262144 : ℝ)/8) ≤ (997969307845480397/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4263/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1516_exp_lower : (920113699314165319/1000000000000000000 : ℝ) ≤ Real.exp ((-10657027886611/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657027886611/16000000000000 : ℝ)/8) ≤ (23002842482854133/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657027886611/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1516_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906027529/1000000000000 : ℝ) ≤ 4*Real.exp (8525/65536 : ℝ)*Real.exp (-mu (radius 8 (4263/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906027529/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4263/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1516_exp_radius
  have hrNumeric : (491934729453/500000000000 : ℝ) ≤ Real.exp (-4263/262144 : ℝ) ∧ Real.exp (-4263/262144 : ℝ) ≤ (983869458907/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491934729453/500000000000 : ℝ) ≤ (radius 8 (4263/32768 : ℝ)) ∧ (radius 8 (4263/32768 : ℝ)) ≤ (983869458907/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4263/32768 : ℝ)) (491934729453/500000000000 : ℝ) (983869458907/1000000000000 : ℝ) (178887919743/1000000000000 : ℝ) (178887919749/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4263/32768 : ℝ)) (491934729453/500000000000 : ℝ) (983869458907/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4263/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491934729453/500000000000 : ℝ) (983869458907/1000000000000 : ℝ) (991934729453/1000000000000 : ℝ) (495967364727/500000000000 : ℝ) (495950970083/500000000000 : ℝ) (991901940167/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4263/32768 : ℝ)) 1 (991934729453/1000000000000 : ℝ) (495967364727/500000000000 : ℝ) (495950970083/500000000000 : ℝ) (991901940167/1000000000000 : ℝ) (991918334809/1000000000000 : ℝ) (991918334811/1000000000000 : ℝ) (495959167337/500000000000 : ℝ) (247979583669/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4263/32768 : ℝ)) 2 (991918334809/1000000000000 : ℝ) (991918334811/1000000000000 : ℝ) (495959167337/500000000000 : ℝ) (247979583669/250000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4263/32768 : ℝ)) 3 (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4263/32768 : ℝ)) 4 (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4263/32768 : ℝ)) 5 (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4263/32768 : ℝ)) 6 (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4263/32768 : ℝ)) 7 (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4263/32768 : ℝ))) (178887919743/1000000000000 : ℝ) (178887919749/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4263/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178887919743/1000000000000 : ℝ) (178887919749/1000000000000 : ℝ) (589443959871/1000000000000 : ℝ) (4715551679/8000000000 : ℝ) (422951438989/1000000000000 : ℝ) (422951438997/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4263/32768 : ℝ))) 1 (589443959871/1000000000000 : ℝ) (4715551679/8000000000 : ℝ) (422951438989/1000000000000 : ℝ) (422951438997/1000000000000 : ℝ) (50619769943/100000000000 : ℝ) (126549424859/250000000000 : ℝ) (249652844481/500000000000 : ℝ) (49930568897/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4263/32768 : ℝ))) 2 (50619769943/100000000000 : ℝ) (126549424859/250000000000 : ℝ) (249652844481/500000000000 : ℝ) (49930568897/100000000000 : ℝ) (125687923549/250000000000 : ℝ) (502751694203/1000000000000 : ℝ) (502739884099/1000000000000 : ℝ) (125684971027/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4263/32768 : ℝ))) 3 (125687923549/250000000000 : ℝ) (502751694203/1000000000000 : ℝ) (502739884099/1000000000000 : ℝ) (125684971027/250000000000 : ℝ) (502745789147/1000000000000 : ℝ) (125686447289/250000000000 : ℝ) (62843223639/125000000000 : ℝ) (502745789121/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4263/32768 : ℝ))) 4 (502745789147/1000000000000 : ℝ) (125686447289/250000000000 : ℝ) (62843223639/125000000000 : ℝ) (502745789121/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4263/32768 : ℝ))) 5 (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4263/32768 : ℝ))) 6 (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4263/32768 : ℝ))) 7 (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4263/32768 : ℝ)) hmem 8 (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4263/32768 : ℝ))) hcmem 8 (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4263/32768 : ℝ)) (991918334741/1000000000000 : ℝ) (123989791843/125000000000 : ℝ) (502745789129/1000000000000 : ℝ) (502745789139/1000000000000 : ℝ) (199036354913/250000000000 : ℝ) (796145419671/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1516_exp_lower
  have heNumeric : (2054906027529/1000000000000 : ℝ)/4 ≤ Real.exp (-10657027886611/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906027529/1000000000000 : ℝ)/4 ≤ Real.exp ((8525/65536 : ℝ)-(796145419671/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8525/65536 : ℝ) (4263/32768 : ℝ) (796145419671/1000000000000 : ℝ) (2054906027529/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1517; no trusted numerical premise.
theorem cover8_leaf1517_exp_radius : (249492267477771099/250000000000000000 : ℝ) ≤ Real.exp ((-8527/524288 : ℝ)/8) ∧ Real.exp ((-8527/524288 : ℝ)/8) ≤ (997969069911084397/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8527/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1517_exp_lower : (920113721688462591/1000000000000000000 : ℝ) ≤ Real.exp ((-213140495481/320000000000 : ℝ)/8) ∧ Real.exp ((-213140495481/320000000000 : ℝ)/8) ≤ (3594194225345557/3906250000000000 : ℝ) := by
  have h := exp_small_bounds ((-213140495481/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1517_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906427281/1000000000000 : ℝ) ≤ 4*Real.exp (4263/32768 : ℝ)*Real.exp (-mu (radius 8 (8527/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906427281/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8527/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1517_exp_radius
  have hrNumeric : (491933791163/500000000000 : ℝ) ≤ Real.exp (-8527/524288 : ℝ) ∧ Real.exp (-8527/524288 : ℝ) ≤ (983867582327/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491933791163/500000000000 : ℝ) ≤ (radius 8 (8527/65536 : ℝ)) ∧ (radius 8 (8527/65536 : ℝ)) ≤ (983867582327/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8527/65536 : ℝ)) (491933791163/500000000000 : ℝ) (983867582327/1000000000000 : ℝ) (178898240477/1000000000000 : ℝ) (44724560121/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8527/65536 : ℝ)) (491933791163/500000000000 : ℝ) (983867582327/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8527/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491933791163/500000000000 : ℝ) (983867582327/1000000000000 : ℝ) (991933791163/1000000000000 : ℝ) (247983447791/250000000000 : ℝ) (198380198843/200000000000 : ℝ) (991900994217/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8527/65536 : ℝ)) 1 (991933791163/1000000000000 : ℝ) (247983447791/250000000000 : ℝ) (198380198843/200000000000 : ℝ) (991900994217/1000000000000 : ℝ) (991917392689/1000000000000 : ℝ) (991917392691/1000000000000 : ℝ) (991917392553/1000000000000 : ℝ) (198383478511/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8527/65536 : ℝ)) 2 (991917392689/1000000000000 : ℝ) (991917392691/1000000000000 : ℝ) (991917392553/1000000000000 : ℝ) (198383478511/200000000000 : ℝ) (991917392621/1000000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8527/65536 : ℝ)) 3 (991917392621/1000000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8527/65536 : ℝ)) 4 (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8527/65536 : ℝ)) 5 (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8527/65536 : ℝ)) 6 (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8527/65536 : ℝ)) 7 (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8527/65536 : ℝ))) (178898240477/1000000000000 : ℝ) (44724560121/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8527/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178898240477/1000000000000 : ℝ) (44724560121/250000000000 : ℝ) (294724560119/500000000000 : ℝ) (294724560121/500000000000 : ℝ) (422963639663/1000000000000 : ℝ) (52870454959/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8527/65536 : ℝ))) 1 (294724560119/500000000000 : ℝ) (294724560121/500000000000 : ℝ) (422963639663/1000000000000 : ℝ) (52870454959/125000000000 : ℝ) (10124127599/20000000000 : ℝ) (506206379957/1000000000000 : ℝ) (499315076171/1000000000000 : ℝ) (499315076179/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8527/65536 : ℝ))) 2 (10124127599/20000000000 : ℝ) (506206379957/1000000000000 : ℝ) (499315076171/1000000000000 : ℝ) (499315076179/1000000000000 : ℝ) (25138036403/50000000000 : ℝ) (125690182017/250000000000 : ℝ) (251374460299/500000000000 : ℝ) (502748920607/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8527/65536 : ℝ))) 3 (25138036403/50000000000 : ℝ) (125690182017/250000000000 : ℝ) (251374460299/500000000000 : ℝ) (502748920607/1000000000000 : ℝ) (502754824329/1000000000000 : ℝ) (251377412169/500000000000 : ℝ) (251377412147/500000000000 : ℝ) (502754824303/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8527/65536 : ℝ))) 4 (502754824329/1000000000000 : ℝ) (251377412169/500000000000 : ℝ) (251377412147/500000000000 : ℝ) (502754824303/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8527/65536 : ℝ))) 5 (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8527/65536 : ℝ))) 6 (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8527/65536 : ℝ))) 7 (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8527/65536 : ℝ)) hmem 8 (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8527/65536 : ℝ))) hcmem 8 (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8527/65536 : ℝ)) (49595869631/50000000000 : ℝ) (991917392623/1000000000000 : ℝ) (502754824311/1000000000000 : ℝ) (502754824321/1000000000000 : ℝ) (398080241953/500000000000 : ℝ) (31846419357/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1517_exp_lower
  have heNumeric : (2054906427281/1000000000000 : ℝ)/4 ≤ Real.exp (-213140495481/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906427281/1000000000000 : ℝ)/4 ≤ Real.exp ((4263/32768 : ℝ)-(31846419357/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4263/32768 : ℝ) (8527/65536 : ℝ) (31846419357/40000000000 : ℝ) (2054906427281/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1518; no trusted numerical premise.
theorem cover8_leaf1518_exp_radius : (7983750655813961/8000000000000000 : ℝ) ≤ Real.exp ((-533/32768 : ℝ)/8) ∧ Real.exp ((-533/32768 : ℝ)/8) ≤ (498984415988372563/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-533/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1518_exp_lower : (184022748839971471/200000000000000000 : ℝ) ≤ Real.exp ((-10657021642417/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657021642417/16000000000000 : ℝ)/8) ≤ (230028436049964339/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657021642417/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1518_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453414741/500000000000 : ℝ) ≤ 4*Real.exp (8527/65536 : ℝ)*Real.exp (-mu (radius 8 (533/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453414741/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (533/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1518_exp_radius
  have hrNumeric : (983865705749/1000000000000 : ℝ) ≤ Real.exp (-533/32768 : ℝ) ∧ Real.exp (-533/32768 : ℝ) ≤ (3935462823/4000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983865705749/1000000000000 : ℝ) ≤ (radius 8 (533/4096 : ℝ)) ∧ (radius 8 (533/4096 : ℝ)) ≤ (3935462823/4000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (533/4096 : ℝ)) (983865705749/1000000000000 : ℝ) (3935462823/4000000000 : ℝ) (8945428029/50000000000 : ℝ) (178908560587/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (533/4096 : ℝ)) (983865705749/1000000000000 : ℝ) (3935462823/4000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (533/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983865705749/1000000000000 : ℝ) (3935462823/4000000000 : ℝ) (495966426437/500000000000 : ℝ) (7935462823/8000000000 : ℝ) (198380009653/200000000000 : ℝ) (495950024133/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (533/4096 : ℝ)) 1 (495966426437/500000000000 : ℝ) (7935462823/8000000000 : ℝ) (198380009653/200000000000 : ℝ) (495950024133/500000000000 : ℝ) (991916450569/1000000000000 : ℝ) (991916450571/1000000000000 : ℝ) (991916450433/1000000000000 : ℝ) (198383290087/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (533/4096 : ℝ)) 2 (991916450569/1000000000000 : ℝ) (991916450571/1000000000000 : ℝ) (991916450433/1000000000000 : ℝ) (198383290087/200000000000 : ℝ) (991916450501/1000000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (533/4096 : ℝ)) 3 (991916450501/1000000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (533/4096 : ℝ)) 4 (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (533/4096 : ℝ)) 5 (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (533/4096 : ℝ)) 6 (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (533/4096 : ℝ)) 7 (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (533/4096 : ℝ))) (8945428029/50000000000 : ℝ) (178908560587/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (533/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8945428029/50000000000 : ℝ) (178908560587/1000000000000 : ℝ) (58945428029/100000000000 : ℝ) (294727140147/500000000000 : ℝ) (422975839239/1000000000000 : ℝ) (26435989953/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (533/4096 : ℝ))) 1 (58945428029/100000000000 : ℝ) (294727140147/500000000000 : ℝ) (422975839239/1000000000000 : ℝ) (26435989953/62500000000 : ℝ) (126553764941/250000000000 : ℝ) (506215059771/1000000000000 : ℝ) (499324462547/1000000000000 : ℝ) (99864892511/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (533/4096 : ℝ))) 2 (126553764941/250000000000 : ℝ) (506215059771/1000000000000 : ℝ) (499324462547/1000000000000 : ℝ) (99864892511/200000000000 : ℝ) (100553952231/200000000000 : ℝ) (502769761163/1000000000000 : ℝ) (251378978163/500000000000 : ℝ) (100551591267/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (533/4096 : ℝ))) 3 (100553952231/200000000000 : ℝ) (502769761163/1000000000000 : ℝ) (251378978163/500000000000 : ℝ) (100551591267/200000000000 : ℝ) (25138192937/50000000000 : ℝ) (502763858749/1000000000000 : ℝ) (100552771741/200000000000 : ℝ) (100552771743/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (533/4096 : ℝ))) 4 (25138192937/50000000000 : ℝ) (502763858749/1000000000000 : ℝ) (100552771741/200000000000 : ℝ) (100552771743/200000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (533/4096 : ℝ))) 5 (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (533/4096 : ℝ))) 6 (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (533/4096 : ℝ))) 7 (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (533/4096 : ℝ)) hmem 8 (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (533/4096 : ℝ))) hcmem 8 (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (533/4096 : ℝ)) (1983832901/2000000000 : ℝ) (991916450503/1000000000000 : ℝ) (251381929361/500000000000 : ℝ) (125690964683/250000000000 : ℝ) (796175546967/1000000000000 : ℝ) (796175546987/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1518_exp_lower
  have heNumeric : (1027453414741/500000000000 : ℝ)/4 ≤ Real.exp (-10657021642417/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453414741/500000000000 : ℝ)/4 ≤ Real.exp ((8527/65536 : ℝ)-(796175546987/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8527/65536 : ℝ) (533/4096 : ℝ) (796175546987/1000000000000 : ℝ) (1027453414741/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1519; no trusted numerical premise.
theorem cover8_leaf1519_exp_radius : (997968594042462581/1000000000000000000 : ℝ) ≤ Real.exp ((-8529/524288 : ℝ)/8) ∧ Real.exp ((-8529/524288 : ℝ)/8) ≤ (498984297021231291/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8529/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1519_exp_lower : (115014220856158717/125000000000000000 : ℝ) ≤ Real.exp ((-166515913931/250000000000 : ℝ)/8) ∧ Real.exp ((-166515913931/250000000000 : ℝ)/8) ≤ (920113766849269737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166515913931/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1519_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726808537/250000000000 : ℝ) ≤ 4*Real.exp (533/4096 : ℝ)*Real.exp (-mu (radius 8 (8529/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513726808537/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8529/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1519_exp_radius
  have hrNumeric : (122982978647/125000000000 : ℝ) ≤ Real.exp (-8529/524288 : ℝ) ∧ Real.exp (-8529/524288 : ℝ) ≤ (983863829177/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122982978647/125000000000 : ℝ) ≤ (radius 8 (8529/65536 : ℝ)) ∧ (radius 8 (8529/65536 : ℝ)) ≤ (983863829177/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8529/65536 : ℝ)) (122982978647/125000000000 : ℝ) (983863829177/1000000000000 : ℝ) (89459440023/500000000000 : ℝ) (178918880053/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8529/65536 : ℝ)) (122982978647/125000000000 : ℝ) (983863829177/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8529/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122982978647/125000000000 : ℝ) (983863829177/1000000000000 : ℝ) (247982978647/250000000000 : ℝ) (991931914589/1000000000000 : ℝ) (247974775579/250000000000 : ℝ) (991899102317/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8529/65536 : ℝ)) 1 (247982978647/250000000000 : ℝ) (991931914589/1000000000000 : ℝ) (247974775579/250000000000 : ℝ) (991899102317/1000000000000 : ℝ) (247978877113/250000000000 : ℝ) (991915508453/1000000000000 : ℝ) (247978877079/250000000000 : ℝ) (495957754159/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8529/65536 : ℝ)) 2 (247978877113/250000000000 : ℝ) (991915508453/1000000000000 : ℝ) (247978877079/250000000000 : ℝ) (495957754159/500000000000 : ℝ) (30997359637/31250000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8529/65536 : ℝ)) 3 (30997359637/31250000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8529/65536 : ℝ)) 4 (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8529/65536 : ℝ)) 5 (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8529/65536 : ℝ)) 6 (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8529/65536 : ℝ)) 7 (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8529/65536 : ℝ))) (89459440023/500000000000 : ℝ) (178918880053/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8529/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89459440023/500000000000 : ℝ) (178918880053/1000000000000 : ℝ) (589459440023/1000000000000 : ℝ) (589459440027/1000000000000 : ℝ) (42298803771/100000000000 : ℝ) (422988037719/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8529/65536 : ℝ))) 1 (589459440023/1000000000000 : ℝ) (589459440027/1000000000000 : ℝ) (42298803771/100000000000 : ℝ) (422988037719/1000000000000 : ℝ) (253111869433/500000000000 : ℝ) (506223738873/1000000000000 : ℝ) (249666924043/500000000000 : ℝ) (249666924047/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8529/65536 : ℝ))) 2 (253111869433/500000000000 : ℝ) (506223738873/1000000000000 : ℝ) (249666924043/500000000000 : ℝ) (249666924047/500000000000 : ℝ) (125694698369/250000000000 : ℝ) (125694698371/250000000000 : ℝ) (502766991279/1000000000000 : ℝ) (62845873911/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8529/65536 : ℝ))) 3 (125694698369/250000000000 : ℝ) (125694698371/250000000000 : ℝ) (502766991279/1000000000000 : ℝ) (62845873911/125000000000 : ℝ) (502772892377/1000000000000 : ℝ) (251386446193/500000000000 : ℝ) (251386446171/500000000000 : ℝ) (7855826443/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8529/65536 : ℝ))) 4 (502772892377/1000000000000 : ℝ) (251386446193/500000000000 : ℝ) (251386446171/500000000000 : ℝ) (7855826443/15625000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8529/65536 : ℝ))) 5 (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8529/65536 : ℝ))) 6 (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8529/65536 : ℝ))) 7 (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8529/65536 : ℝ)) hmem 8 (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8529/65536 : ℝ))) hcmem 8 (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8529/65536 : ℝ)) (991915508383/1000000000000 : ℝ) (495957754193/500000000000 : ℝ) (502772892359/1000000000000 : ℝ) (502772892369/1000000000000 : ℝ) (796190608829/1000000000000 : ℝ) (796190608849/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1519_exp_lower
  have heNumeric : (513726808537/250000000000 : ℝ)/4 ≤ Real.exp (-166515913931/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726808537/250000000000 : ℝ)/4 ≤ Real.exp ((533/4096 : ℝ)-(796190608849/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (533/4096 : ℝ) (8529/65536 : ℝ) (796190608849/1000000000000 : ℝ) (513726808537/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1520; no trusted numerical premise.
theorem cover8_leaf1520_exp_radius : (199593671221647353/200000000000000000 : ℝ) ≤ Real.exp ((-4265/262144 : ℝ)/8) ∧ Real.exp ((-4265/262144 : ℝ)/8) ≤ (498984178054118383/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4265/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1520_exp_lower : (460056894817947321/500000000000000000 : ℝ) ≤ Real.exp ((-10657015321663/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657015321663/16000000000000 : ℝ)/8) ≤ (920113789635894643/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657015321663/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1520_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054907641267/1000000000000 : ℝ) ≤ 4*Real.exp (8529/65536 : ℝ)*Real.exp (-mu (radius 8 (4265/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054907641267/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4265/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1520_exp_radius
  have hrNumeric : (491930976303/500000000000 : ℝ) ≤ Real.exp (-4265/262144 : ℝ) ∧ Real.exp (-4265/262144 : ℝ) ≤ (983861952607/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491930976303/500000000000 : ℝ) ≤ (radius 8 (4265/32768 : ℝ)) ∧ (radius 8 (4265/32768 : ℝ)) ≤ (983861952607/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4265/32768 : ℝ)) (491930976303/500000000000 : ℝ) (983861952607/1000000000000 : ℝ) (178929198881/1000000000000 : ℝ) (178929198887/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4265/32768 : ℝ)) (491930976303/500000000000 : ℝ) (983861952607/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4265/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491930976303/500000000000 : ℝ) (983861952607/1000000000000 : ℝ) (991930976303/1000000000000 : ℝ) (61995686019/62500000000 : ℝ) (991898156367/1000000000000 : ℝ) (991898156369/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4265/32768 : ℝ)) 1 (991930976303/1000000000000 : ℝ) (61995686019/62500000000 : ℝ) (991898156367/1000000000000 : ℝ) (991898156369/1000000000000 : ℝ) (198382913267/200000000000 : ℝ) (991914566337/1000000000000 : ℝ) (991914566199/1000000000000 : ℝ) (991914566201/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4265/32768 : ℝ)) 2 (198382913267/200000000000 : ℝ) (991914566337/1000000000000 : ℝ) (991914566199/1000000000000 : ℝ) (991914566201/1000000000000 : ℝ) (991914566267/1000000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4265/32768 : ℝ)) 3 (991914566267/1000000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4265/32768 : ℝ)) 4 (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4265/32768 : ℝ)) 5 (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4265/32768 : ℝ)) 6 (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4265/32768 : ℝ)) 7 (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4265/32768 : ℝ))) (178929198881/1000000000000 : ℝ) (178929198887/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4265/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178929198881/1000000000000 : ℝ) (178929198887/1000000000000 : ℝ) (7368307493/12500000000 : ℝ) (147366149861/250000000000 : ℝ) (423000235083/1000000000000 : ℝ) (423000235091/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4265/32768 : ℝ))) 1 (7368307493/12500000000 : ℝ) (147366149861/250000000000 : ℝ) (423000235083/1000000000000 : ℝ) (423000235091/1000000000000 : ℝ) (506232417261/1000000000000 : ℝ) (126558104317/250000000000 : ℝ) (499343232793/1000000000000 : ℝ) (624179041/1250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4265/32768 : ℝ))) 2 (506232417261/1000000000000 : ℝ) (126558104317/250000000000 : ℝ) (499343232793/1000000000000 : ℝ) (624179041/1250000000 : ℝ) (502787825027/1000000000000 : ℝ) (251393912517/500000000000 : ℝ) (251388012731/500000000000 : ℝ) (50277602547/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4265/32768 : ℝ))) 3 (502787825027/1000000000000 : ℝ) (251393912517/500000000000 : ℝ) (251388012731/500000000000 : ℝ) (50277602547/100000000000 : ℝ) (125695481311/250000000000 : ℝ) (125695481313/250000000000 : ℝ) (502781925209/1000000000000 : ℝ) (251390962609/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4265/32768 : ℝ))) 4 (125695481311/250000000000 : ℝ) (125695481313/250000000000 : ℝ) (502781925209/1000000000000 : ℝ) (251390962609/500000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4265/32768 : ℝ))) 5 (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4265/32768 : ℝ))) 6 (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4265/32768 : ℝ))) 7 (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4265/32768 : ℝ)) hmem 8 (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4265/32768 : ℝ))) hcmem 8 (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4265/32768 : ℝ)) (495957283133/500000000000 : ℝ) (991914566269/1000000000000 : ℝ) (251390962613/500000000000 : ℝ) (100556385047/200000000000 : ℝ) (1592411339/2000000000 : ℝ) (398102834759/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1520_exp_lower
  have heNumeric : (2054907641267/1000000000000 : ℝ)/4 ≤ Real.exp (-10657015321663/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054907641267/1000000000000 : ℝ)/4 ≤ Real.exp ((8529/65536 : ℝ)-(398102834759/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8529/65536 : ℝ) (4265/32768 : ℝ) (398102834759/500000000000 : ℝ) (2054907641267/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1521; no trusted numerical premise.
theorem cover8_leaf1521_exp_radius : (498984059087033839/500000000000000000 : ℝ) ≤ Real.exp ((-8531/524288 : ℝ)/8) ∧ Real.exp ((-8531/524288 : ℝ)/8) ≤ (997968118174067679/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8531/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1521_exp_lower : (460056906280096071/500000000000000000 : ℝ) ≤ Real.exp ((-1065701213259/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065701213259/1600000000000 : ℝ)/8) ≤ (920113812560192143/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065701213259/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1521_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981610169/200000000000 : ℝ) ≤ 4*Real.exp (4265/32768 : ℝ)*Real.exp (-mu (radius 8 (8531/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410981610169/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8531/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1521_exp_radius
  have hrNumeric : (24596501901/25000000000 : ℝ) ≤ Real.exp (-8531/524288 : ℝ) ∧ Real.exp (-8531/524288 : ℝ) ≤ (983860076041/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24596501901/25000000000 : ℝ) ≤ (radius 8 (8531/65536 : ℝ)) ∧ (radius 8 (8531/65536 : ℝ)) ≤ (983860076041/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8531/65536 : ℝ)) (24596501901/25000000000 : ℝ) (983860076041/1000000000000 : ℝ) (178939517079/1000000000000 : ℝ) (35787903417/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8531/65536 : ℝ)) (24596501901/25000000000 : ℝ) (983860076041/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8531/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24596501901/25000000000 : ℝ) (983860076041/1000000000000 : ℝ) (49596501901/50000000000 : ℝ) (991930038021/1000000000000 : ℝ) (49594860521/50000000000 : ℝ) (495948605211/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8531/65536 : ℝ)) 1 (49596501901/50000000000 : ℝ) (991930038021/1000000000000 : ℝ) (49594860521/50000000000 : ℝ) (495948605211/500000000000 : ℝ) (49595681211/50000000000 : ℝ) (495956812111/500000000000 : ℝ) (247978406021/250000000000 : ℝ) (495956812043/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8531/65536 : ℝ)) 2 (49595681211/50000000000 : ℝ) (495956812111/500000000000 : ℝ) (247978406021/250000000000 : ℝ) (495956812043/500000000000 : ℝ) (123989203019/125000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8531/65536 : ℝ)) 3 (123989203019/125000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8531/65536 : ℝ)) 4 (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8531/65536 : ℝ)) 5 (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8531/65536 : ℝ)) 6 (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8531/65536 : ℝ)) 7 (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8531/65536 : ℝ))) (178939517079/1000000000000 : ℝ) (35787903417/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8531/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178939517079/1000000000000 : ℝ) (35787903417/200000000000 : ℝ) (589469758539/1000000000000 : ℝ) (589469758543/1000000000000 : ℝ) (52876553919/125000000000 : ℝ) (165239231/390625000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8531/65536 : ℝ))) 1 (589469758539/1000000000000 : ℝ) (589469758543/1000000000000 : ℝ) (52876553919/125000000000 : ℝ) (165239231/390625000 : ℝ) (101248218989/200000000000 : ℝ) (63280136869/125000000000 : ℝ) (249676308331/500000000000 : ℝ) (49935261667/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8531/65536 : ℝ))) 2 (101248218989/200000000000 : ℝ) (63280136869/125000000000 : ℝ) (249676308331/500000000000 : ℝ) (49935261667/100000000000 : ℝ) (502796855803/1000000000000 : ℝ) (502796855811/1000000000000 : ℝ) (502785058869/1000000000000 : ℝ) (251392529439/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8531/65536 : ℝ))) 3 (502796855803/1000000000000 : ℝ) (502796855811/1000000000000 : ℝ) (502785058869/1000000000000 : ℝ) (251392529439/500000000000 : ℝ) (62848869667/125000000000 : ℝ) (100558191469/200000000000 : ℝ) (502790957301/1000000000000 : ℝ) (50279095731/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8531/65536 : ℝ))) 4 (62848869667/125000000000 : ℝ) (100558191469/200000000000 : ℝ) (502790957301/1000000000000 : ℝ) (50279095731/100000000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8531/65536 : ℝ))) 5 (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8531/65536 : ℝ))) 6 (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8531/65536 : ℝ))) 7 (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8531/65536 : ℝ)) hmem 8 (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8531/65536 : ℝ))) hcmem 8 (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8531/65536 : ℝ)) (991913624151/1000000000000 : ℝ) (495956812077/500000000000 : ℝ) (251395478659/500000000000 : ℝ) (31424434833/62500000000 : ℝ) (796220728971/1000000000000 : ℝ) (79622072899/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1521_exp_lower
  have heNumeric : (410981610169/200000000000 : ℝ)/4 ≤ Real.exp (-1065701213259/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981610169/200000000000 : ℝ)/4 ≤ Real.exp ((4265/32768 : ℝ)-(79622072899/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4265/32768 : ℝ) (8531/65536 : ℝ) (79622072899/100000000000 : ℝ) (410981610169/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1522; no trusted numerical premise.
theorem cover8_leaf1522_exp_radius : (498983940119977659/500000000000000000 : ℝ) ≤ Real.exp ((-2133/131072 : ℝ)/8) ∧ Real.exp ((-2133/131072 : ℝ)/8) ≤ (997967880239955319/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2133/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1522_exp_lower : (460056917811196137/500000000000000000 : ℝ) ≤ Real.exp ((-10657008924333/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657008924333/16000000000000 : ℝ)/8) ≤ (36804553424895691/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657008924333/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1522_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054908462887/1000000000000 : ℝ) ≤ 4*Real.exp (8531/65536 : ℝ)*Real.exp (-mu (radius 8 (2133/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054908462887/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2133/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1522_exp_radius
  have hrNumeric : (491929099739/500000000000 : ℝ) ≤ Real.exp (-2133/131072 : ℝ) ∧ Real.exp (-2133/131072 : ℝ) ≤ (983858199479/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491929099739/500000000000 : ℝ) ≤ (radius 8 (2133/16384 : ℝ)) ∧ (radius 8 (2133/16384 : ℝ)) ≤ (983858199479/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2133/16384 : ℝ)) (491929099739/500000000000 : ℝ) (983858199479/1000000000000 : ℝ) (2236872933/12500000000 : ℝ) (178949834647/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2133/16384 : ℝ)) (491929099739/500000000000 : ℝ) (983858199479/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2133/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491929099739/500000000000 : ℝ) (983858199479/1000000000000 : ℝ) (991929099739/1000000000000 : ℝ) (49596454987/50000000000 : ℝ) (495948132237/500000000000 : ℝ) (39675850579/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2133/16384 : ℝ)) 1 (991929099739/1000000000000 : ℝ) (49596454987/50000000000 : ℝ) (495948132237/500000000000 : ℝ) (39675850579/40000000000 : ℝ) (495956341053/500000000000 : ℝ) (247978170527/250000000000 : ℝ) (99191268197/100000000000 : ℝ) (247978170493/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2133/16384 : ℝ)) 2 (495956341053/500000000000 : ℝ) (247978170527/250000000000 : ℝ) (99191268197/100000000000 : ℝ) (247978170493/250000000000 : ℝ) (495956341019/500000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2133/16384 : ℝ)) 3 (495956341019/500000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2133/16384 : ℝ)) 4 (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2133/16384 : ℝ)) 5 (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2133/16384 : ℝ)) 6 (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2133/16384 : ℝ)) 7 (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2133/16384 : ℝ))) (2236872933/12500000000 : ℝ) (178949834647/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2133/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2236872933/12500000000 : ℝ) (178949834647/1000000000000 : ℝ) (14736872933/25000000000 : ℝ) (147368729331/250000000000 : ℝ) (423024626517/1000000000000 : ℝ) (211512313263/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2133/16384 : ℝ))) 1 (14736872933/25000000000 : ℝ) (147368729331/250000000000 : ℝ) (423024626517/1000000000000 : ℝ) (211512313263/500000000000 : ℝ) (253124885959/500000000000 : ℝ) (20249990877/40000000000 : ℝ) (31210124981/62500000000 : ℝ) (62420249963/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2133/16384 : ℝ))) 2 (253124885959/500000000000 : ℝ) (20249990877/40000000000 : ℝ) (31210124981/62500000000 : ℝ) (62420249963/125000000000 : ℝ) (502805885807/1000000000000 : ℝ) (100561177163/200000000000 : ℝ) (502794091503/1000000000000 : ℝ) (502794091511/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2133/16384 : ℝ))) 3 (502805885807/1000000000000 : ℝ) (100561177163/200000000000 : ℝ) (502794091503/1000000000000 : ℝ) (502794091511/1000000000000 : ℝ) (100559997731/200000000000 : ℝ) (502799988663/1000000000000 : ℝ) (25139999431/50000000000 : ℝ) (502799988629/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2133/16384 : ℝ))) 4 (100559997731/200000000000 : ℝ) (502799988663/1000000000000 : ℝ) (25139999431/50000000000 : ℝ) (502799988629/1000000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2133/16384 : ℝ))) 5 (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2133/16384 : ℝ))) 6 (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2133/16384 : ℝ))) 7 (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2133/16384 : ℝ)) hmem 8 (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2133/16384 : ℝ))) hcmem 8 (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2133/16384 : ℝ)) (991912682037/1000000000000 : ℝ) (24797817051/25000000000 : ℝ) (502799988637/1000000000000 : ℝ) (251399994323/500000000000 : ℝ) (398117893623/500000000000 : ℝ) (796235787263/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1522_exp_lower
  have heNumeric : (2054908462887/1000000000000 : ℝ)/4 ≤ Real.exp (-10657008924333/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054908462887/1000000000000 : ℝ)/4 ≤ Real.exp ((8531/65536 : ℝ)-(796235787263/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8531/65536 : ℝ) (2133/16384 : ℝ) (796235787263/1000000000000 : ℝ) (2054908462887/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1523; no trusted numerical premise.
theorem cover8_leaf1523_exp_radius : (498983821152949843/500000000000000000 : ℝ) ≤ Real.exp ((-8533/524288 : ℝ)/8) ∧ Real.exp ((-8533/524288 : ℝ)/8) ≤ (997967642305899687/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8533/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1523_exp_lower : (115014232352696867/125000000000000000 : ℝ) ≤ Real.exp ((-532850284851/800000000000 : ℝ)/8) ∧ Real.exp ((-532850284851/800000000000 : ℝ)/8) ≤ (920113858821574937/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-532850284851/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1523_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054908877377/1000000000000 : ℝ) ≤ 4*Real.exp (2133/16384 : ℝ)*Real.exp (-mu (radius 8 (8533/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054908877377/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8533/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1523_exp_radius
  have hrNumeric : (983856322919/1000000000000 : ℝ) ≤ Real.exp (-8533/524288 : ℝ) ∧ Real.exp (-8533/524288 : ℝ) ≤ (24596408073/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983856322919/1000000000000 : ℝ) ≤ (radius 8 (8533/65536 : ℝ)) ∧ (radius 8 (8533/65536 : ℝ)) ≤ (24596408073/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8533/65536 : ℝ)) (983856322919/1000000000000 : ℝ) (24596408073/25000000000 : ℝ) (178960151571/1000000000000 : ℝ) (178960151577/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8533/65536 : ℝ)) (983856322919/1000000000000 : ℝ) (24596408073/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8533/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983856322919/1000000000000 : ℝ) (24596408073/25000000000 : ℝ) (991928161459/1000000000000 : ℝ) (49596408073/50000000000 : ℝ) (242161943/244140625 : ℝ) (99189531853/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8533/65536 : ℝ)) 1 (991928161459/1000000000000 : ℝ) (49596408073/50000000000 : ℝ) (242161943/244140625 : ℝ) (99189531853/100000000000 : ℝ) (991911739993/1000000000000 : ℝ) (198382347999/200000000000 : ℝ) (991911739857/1000000000000 : ℝ) (49595586993/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8533/65536 : ℝ)) 2 (991911739993/1000000000000 : ℝ) (198382347999/200000000000 : ℝ) (991911739857/1000000000000 : ℝ) (49595586993/50000000000 : ℝ) (39676469597/40000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8533/65536 : ℝ)) 3 (39676469597/40000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8533/65536 : ℝ)) 4 (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8533/65536 : ℝ)) 5 (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8533/65536 : ℝ)) 6 (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8533/65536 : ℝ)) 7 (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8533/65536 : ℝ))) (178960151571/1000000000000 : ℝ) (178960151577/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8533/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178960151571/1000000000000 : ℝ) (178960151577/1000000000000 : ℝ) (117896015157/200000000000 : ℝ) (589480075789/1000000000000 : ℝ) (84607364117/200000000000 : ℝ) (423036820593/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8533/65536 : ℝ))) 1 (117896015157/200000000000 : ℝ) (589480075789/1000000000000 : ℝ) (84607364117/200000000000 : ℝ) (423036820593/1000000000000 : ℝ) (101251689637/200000000000 : ℝ) (506258448191/1000000000000 : ℝ) (499371381897/1000000000000 : ℝ) (31210711369/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8533/65536 : ℝ))) 2 (101251689637/200000000000 : ℝ) (506258448191/1000000000000 : ℝ) (499371381897/1000000000000 : ℝ) (31210711369/62500000000 : ℝ) (502814915041/1000000000000 : ℝ) (62851864381/125000000000 : ℝ) (251401561683/500000000000 : ℝ) (251401561687/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8533/65536 : ℝ))) 3 (502814915041/1000000000000 : ℝ) (62851864381/125000000000 : ℝ) (251401561683/500000000000 : ℝ) (251401561687/500000000000 : ℝ) (502809019203/1000000000000 : ℝ) (502809019211/1000000000000 : ℝ) (15712781849/31250000000 : ℝ) (502809019177/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8533/65536 : ℝ))) 4 (502809019203/1000000000000 : ℝ) (502809019211/1000000000000 : ℝ) (15712781849/31250000000 : ℝ) (502809019177/1000000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8533/65536 : ℝ))) 5 (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8533/65536 : ℝ))) 6 (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8533/65536 : ℝ))) 7 (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8533/65536 : ℝ)) hmem 8 (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8533/65536 : ℝ))) hcmem 8 (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8533/65536 : ℝ)) (247977934981/250000000000 : ℝ) (123988967491/125000000000 : ℝ) (100561803837/200000000000 : ℝ) (251404509597/500000000000 : ℝ) (398125422163/500000000000 : ℝ) (159250168869/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1523_exp_lower
  have heNumeric : (2054908877377/1000000000000 : ℝ)/4 ≤ Real.exp (-532850284851/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054908877377/1000000000000 : ℝ)/4 ≤ Real.exp ((2133/16384 : ℝ)-(159250168869/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2133/16384 : ℝ) (8533/65536 : ℝ) (159250168869/200000000000 : ℝ) (2054908877377/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1524; no trusted numerical premise.
theorem cover8_leaf1524_exp_radius : (498983702185950391/500000000000000000 : ℝ) ≤ Real.exp ((-4267/262144 : ℝ)/8) ∧ Real.exp ((-4267/262144 : ℝ)/8) ≤ (997967404371900783/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4267/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1524_exp_lower : (3680455528634641/4000000000000000 : ℝ) ≤ Real.exp ((-10657002450523/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657002450523/16000000000000 : ℝ)/8) ≤ (920113882158660251/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657002450523/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1524_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490929433/100000000000 : ℝ) ≤ 4*Real.exp (8533/65536 : ℝ)*Real.exp (-mu (radius 8 (4267/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (205490929433/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4267/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1524_exp_radius
  have hrNumeric : (245963611591/250000000000 : ℝ) ≤ Real.exp (-4267/262144 : ℝ) ∧ Real.exp (-4267/262144 : ℝ) ≤ (196770889273/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245963611591/250000000000 : ℝ) ≤ (radius 8 (4267/32768 : ℝ)) ∧ (radius 8 (4267/32768 : ℝ)) ≤ (196770889273/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4267/32768 : ℝ)) (245963611591/250000000000 : ℝ) (196770889273/200000000000 : ℝ) (35794093573/200000000000 : ℝ) (178970467871/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4267/32768 : ℝ)) (245963611591/250000000000 : ℝ) (196770889273/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4267/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245963611591/250000000000 : ℝ) (196770889273/200000000000 : ℝ) (495963611591/500000000000 : ℝ) (991927223183/1000000000000 : ℝ) (123986796573/125000000000 : ℝ) (198378874517/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4267/32768 : ℝ)) 1 (495963611591/500000000000 : ℝ) (991927223183/1000000000000 : ℝ) (123986796573/125000000000 : ℝ) (198378874517/200000000000 : ℝ) (991910797883/1000000000000 : ℝ) (247977699471/250000000000 : ℝ) (991910797747/1000000000000 : ℝ) (991910797749/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4267/32768 : ℝ)) 2 (991910797883/1000000000000 : ℝ) (247977699471/250000000000 : ℝ) (991910797747/1000000000000 : ℝ) (991910797749/1000000000000 : ℝ) (198382159563/200000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4267/32768 : ℝ)) 3 (198382159563/200000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4267/32768 : ℝ)) 4 (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4267/32768 : ℝ)) 5 (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4267/32768 : ℝ)) 6 (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4267/32768 : ℝ)) 7 (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4267/32768 : ℝ))) (35794093573/200000000000 : ℝ) (178970467871/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4267/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35794093573/200000000000 : ℝ) (178970467871/1000000000000 : ℝ) (147371308483/250000000000 : ℝ) (36842827121/62500000000 : ℝ) (423049013549/1000000000000 : ℝ) (423049013557/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4267/32768 : ℝ))) 1 (147371308483/250000000000 : ℝ) (36842827121/62500000000 : ℝ) (423049013549/1000000000000 : ℝ) (423049013557/1000000000000 : ℝ) (25313356187/50000000000 : ℝ) (506267123747/1000000000000 : ℝ) (249690381631/500000000000 : ℝ) (499380763269/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4267/32768 : ℝ))) 2 (25313356187/50000000000 : ℝ) (506267123747/1000000000000 : ℝ) (249690381631/500000000000 : ℝ) (499380763269/1000000000000 : ℝ) (502823943501/1000000000000 : ℝ) (125705985877/250000000000 : ℝ) (100562430891/200000000000 : ℝ) (502812154463/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4267/32768 : ℝ))) 3 (502823943501/1000000000000 : ℝ) (125705985877/250000000000 : ℝ) (100562430891/200000000000 : ℝ) (502812154463/1000000000000 : ℝ) (251409024489/500000000000 : ℝ) (251409024493/500000000000 : ℝ) (502818048943/1000000000000 : ℝ) (502818048951/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4267/32768 : ℝ))) 4 (251409024489/500000000000 : ℝ) (251409024493/500000000000 : ℝ) (502818048943/1000000000000 : ℝ) (502818048951/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4267/32768 : ℝ))) 5 (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4267/32768 : ℝ))) 6 (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4267/32768 : ℝ))) 7 (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4267/32768 : ℝ)) hmem 8 (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4267/32768 : ℝ))) hcmem 8 (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4267/32768 : ℝ)) (495955398907/500000000000 : ℝ) (991910797817/1000000000000 : ℝ) (1571306403/3125000000 : ℝ) (502818048969/1000000000000 : ℝ) (79626590021/100000000000 : ℝ) (199066475057/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1524_exp_lower
  have heNumeric : (205490929433/100000000000 : ℝ)/4 ≤ Real.exp (-10657002450523/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490929433/100000000000 : ℝ)/4 ≤ Real.exp ((8533/65536 : ℝ)-(199066475057/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8533/65536 : ℝ) (4267/32768 : ℝ) (199066475057/250000000000 : ℝ) (205490929433/100000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1500_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1500_certificate
#check SmaleRate.Proofs.cover8_leaf1501_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1501_certificate
#check SmaleRate.Proofs.cover8_leaf1502_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1502_certificate
#check SmaleRate.Proofs.cover8_leaf1503_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1503_certificate
#check SmaleRate.Proofs.cover8_leaf1504_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1504_certificate
#check SmaleRate.Proofs.cover8_leaf1505_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1505_certificate
#check SmaleRate.Proofs.cover8_leaf1506_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1506_certificate
#check SmaleRate.Proofs.cover8_leaf1507_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1507_certificate
#check SmaleRate.Proofs.cover8_leaf1508_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1508_certificate
#check SmaleRate.Proofs.cover8_leaf1509_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1509_certificate
#check SmaleRate.Proofs.cover8_leaf1510_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1510_certificate
#check SmaleRate.Proofs.cover8_leaf1511_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1511_certificate
#check SmaleRate.Proofs.cover8_leaf1512_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1512_certificate
#check SmaleRate.Proofs.cover8_leaf1513_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1513_certificate
#check SmaleRate.Proofs.cover8_leaf1514_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1514_certificate
#check SmaleRate.Proofs.cover8_leaf1515_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1515_certificate
#check SmaleRate.Proofs.cover8_leaf1516_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1516_certificate
#check SmaleRate.Proofs.cover8_leaf1517_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1517_certificate
#check SmaleRate.Proofs.cover8_leaf1518_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1518_certificate
#check SmaleRate.Proofs.cover8_leaf1519_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1519_certificate
#check SmaleRate.Proofs.cover8_leaf1520_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1520_certificate
#check SmaleRate.Proofs.cover8_leaf1521_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1521_certificate
#check SmaleRate.Proofs.cover8_leaf1522_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1522_certificate
#check SmaleRate.Proofs.cover8_leaf1523_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1523_certificate
#check SmaleRate.Proofs.cover8_leaf1524_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1524_certificate
