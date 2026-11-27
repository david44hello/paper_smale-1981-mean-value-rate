/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0525; no trusted numerical premise.
theorem cover8_leaf0525_exp_radius : (199603438659437597/200000000000000000 : ℝ) ≤ Real.exp ((-33299/2097152 : ℝ)/8) ∧ Real.exp ((-33299/2097152 : ℝ)/8) ≤ (499008596648593993/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33299/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0525_exp_lower : (184022714543090857/200000000000000000 : ℝ) ≤ Real.exp ((-17051272797071/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051272797071/25600000000000 : ℝ)/8) ≤ (460056786357727143/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051272797071/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0525_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098075313/20000000000 : ℝ) ≤ 4*Real.exp (66597/524288 : ℝ)*Real.exp (-mu (radius 8 (33299/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (41098075313/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33299/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0525_exp_radius
  have hrNumeric : (49212359677/50000000000 : ℝ) ≤ Real.exp (-33299/2097152 : ℝ) ∧ Real.exp (-33299/2097152 : ℝ) ≤ (984247193541/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49212359677/50000000000 : ℝ) ≤ (radius 8 (33299/262144 : ℝ)) ∧ (radius 8 (33299/262144 : ℝ)) ≤ (984247193541/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33299/262144 : ℝ)) (49212359677/50000000000 : ℝ) (984247193541/1000000000000 : ℝ) (88398899889/500000000000 : ℝ) (35359559957/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33299/262144 : ℝ)) (49212359677/50000000000 : ℝ) (984247193541/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33299/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49212359677/50000000000 : ℝ) (984247193541/1000000000000 : ℝ) (99212359677/100000000000 : ℝ) (992123596771/1000000000000 : ℝ) (248023082789/250000000000 : ℝ) (496046165579/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33299/262144 : ℝ)) 1 (99212359677/100000000000 : ℝ) (992123596771/1000000000000 : ℝ) (248023082789/250000000000 : ℝ) (496046165579/500000000000 : ℝ) (992107963963/1000000000000 : ℝ) (198421592793/200000000000 : ℝ) (992107963839/1000000000000 : ℝ) (496053981921/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33299/262144 : ℝ)) 2 (992107963963/1000000000000 : ℝ) (198421592793/200000000000 : ℝ) (992107963839/1000000000000 : ℝ) (496053981921/500000000000 : ℝ) (992107963901/1000000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33299/262144 : ℝ)) 3 (992107963901/1000000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33299/262144 : ℝ)) 4 (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33299/262144 : ℝ)) 5 (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33299/262144 : ℝ)) 6 (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33299/262144 : ℝ)) 7 (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33299/262144 : ℝ))) (88398899889/500000000000 : ℝ) (35359559957/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33299/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88398899889/500000000000 : ℝ) (35359559957/200000000000 : ℝ) (588398899889/1000000000000 : ℝ) (588398899893/1000000000000 : ℝ) (420473304477/1000000000000 : ℝ) (210236652243/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33299/262144 : ℝ))) 1 (588398899889/1000000000000 : ℝ) (588398899893/1000000000000 : ℝ) (420473304477/1000000000000 : ℝ) (210236652243/500000000000 : ℝ) (504436102183/1000000000000 : ℝ) (50443610219/100000000000 : ℝ) (497399265969/1000000000000 : ℝ) (497399265977/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33299/262144 : ℝ))) 2 (504436102183/1000000000000 : ℝ) (50443610219/100000000000 : ℝ) (497399265969/1000000000000 : ℝ) (497399265977/1000000000000 : ℝ) (125229421019/250000000000 : ℝ) (125229421021/250000000000 : ℝ) (62613165917/125000000000 : ℝ) (100181065469/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33299/262144 : ℝ))) 3 (125229421019/250000000000 : ℝ) (125229421021/250000000000 : ℝ) (62613165917/125000000000 : ℝ) (100181065469/200000000000 : ℝ) (250455752853/500000000000 : ℝ) (100182301143/200000000000 : ℝ) (500911505667/1000000000000 : ℝ) (500911505677/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33299/262144 : ℝ))) 4 (250455752853/500000000000 : ℝ) (100182301143/200000000000 : ℝ) (500911505667/1000000000000 : ℝ) (500911505677/1000000000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33299/262144 : ℝ))) 5 (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33299/262144 : ℝ))) 6 (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33299/262144 : ℝ))) 7 (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33299/262144 : ℝ)) hmem 8 (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33299/262144 : ℝ))) hcmem 8 (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33299/262144 : ℝ)) (9921079639/10000000000 : ℝ) (1937710867/1953125000 : ℝ) (250455752843/500000000000 : ℝ) (15653484553/31250000000 : ℝ) (158617808103/200000000000 : ℝ) (158617808107/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0525_exp_lower
  have heNumeric : (41098075313/20000000000 : ℝ)/4 ≤ Real.exp (-17051272797071/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098075313/20000000000 : ℝ)/4 ≤ Real.exp ((66597/524288 : ℝ)-(158617808107/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66597/524288 : ℝ) (33299/262144 : ℝ) (158617808107/200000000000 : ℝ) (41098075313/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0526; no trusted numerical premise.
theorem cover8_leaf0526_exp_radius : (199603432710791657/200000000000000000 : ℝ) ≤ Real.exp ((-66599/4194304 : ℝ)/8) ∧ Real.exp ((-66599/4194304 : ℝ)/8) ≤ (499008581776979143/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66599/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0526_exp_lower : (920113571968509861/1000000000000000000 : ℝ) ≤ Real.exp ((-42628182408317/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628182408317/64000000000000 : ℝ)/8) ≤ (460056785984254931/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628182408317/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0526_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431484519/62500000000 : ℝ) ≤ 4*Real.exp (33299/262144 : ℝ)*Real.exp (-mu (radius 8 (66599/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431484519/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66599/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0526_exp_radius
  have hrNumeric : (984246958877/1000000000000 : ℝ) ≤ Real.exp (-66599/4194304 : ℝ) ∧ Real.exp (-66599/4194304 : ℝ) ≤ (492123479439/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984246958877/1000000000000 : ℝ) ≤ (radius 8 (66599/524288 : ℝ)) ∧ (radius 8 (66599/524288 : ℝ)) ≤ (492123479439/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66599/524288 : ℝ)) (984246958877/1000000000000 : ℝ) (492123479439/500000000000 : ℝ) (176799106161/1000000000000 : ℝ) (176799106167/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66599/524288 : ℝ)) (984246958877/1000000000000 : ℝ) (492123479439/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66599/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984246958877/1000000000000 : ℝ) (492123479439/500000000000 : ℝ) (496061739719/500000000000 : ℝ) (992123479439/1000000000000 : ℝ) (99209221289/100000000000 : ℝ) (992092212891/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66599/524288 : ℝ)) 1 (496061739719/500000000000 : ℝ) (992123479439/1000000000000 : ℝ) (99209221289/100000000000 : ℝ) (992092212891/1000000000000 : ℝ) (248026961541/250000000000 : ℝ) (198421569233/200000000000 : ℝ) (24802696151/25000000000 : ℝ) (496053923021/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66599/524288 : ℝ)) 2 (248026961541/250000000000 : ℝ) (198421569233/200000000000 : ℝ) (24802696151/25000000000 : ℝ) (496053923021/500000000000 : ℝ) (496053923051/500000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66599/524288 : ℝ)) 3 (496053923051/500000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66599/524288 : ℝ)) 4 (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66599/524288 : ℝ)) 5 (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66599/524288 : ℝ)) 6 (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66599/524288 : ℝ)) 7 (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66599/524288 : ℝ))) (176799106161/1000000000000 : ℝ) (176799106167/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66599/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176799106161/1000000000000 : ℝ) (176799106167/1000000000000 : ℝ) (14709988827/25000000000 : ℝ) (147099888271/250000000000 : ℝ) (420474857941/1000000000000 : ℝ) (420474857949/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66599/524288 : ℝ))) 1 (14709988827/25000000000 : ℝ) (147099888271/250000000000 : ℝ) (420474857941/1000000000000 : ℝ) (420474857949/1000000000000 : ℝ) (50443720551/100000000000 : ℝ) (504437205517/1000000000000 : ℝ) (49740046089/100000000000 : ℝ) (497400460897/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66599/524288 : ℝ))) 2 (50443720551/100000000000 : ℝ) (504437205517/1000000000000 : ℝ) (49740046089/100000000000 : ℝ) (497400460897/1000000000000 : ℝ) (1252297083/2500000000 : ℝ) (500918833207/1000000000000 : ℝ) (50090647681/100000000000 : ℝ) (250453238409/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66599/524288 : ℝ))) 3 (1252297083/2500000000 : ℝ) (500918833207/1000000000000 : ℝ) (50090647681/100000000000 : ℝ) (250453238409/500000000000 : ℝ) (100182531001/200000000000 : ℝ) (500912655013/1000000000000 : ℝ) (250456327483/500000000000 : ℝ) (20036506199/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66599/524288 : ℝ))) 4 (100182531001/200000000000 : ℝ) (500912655013/1000000000000 : ℝ) (250456327483/500000000000 : ℝ) (20036506199/40000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66599/524288 : ℝ))) 5 (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66599/524288 : ℝ))) 6 (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66599/524288 : ℝ))) 7 (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66599/524288 : ℝ)) hmem 8 (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66599/524288 : ℝ))) hcmem 8 (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66599/524288 : ℝ)) (992107846101/1000000000000 : ℝ) (124013480763/125000000000 : ℝ) (100182530997/200000000000 : ℝ) (250456327497/500000000000 : ℝ) (19827273859/25000000000 : ℝ) (396545477189/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0526_exp_lower
  have heNumeric : (128431484519/62500000000 : ℝ)/4 ≤ Real.exp (-42628182408317/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431484519/62500000000 : ℝ)/4 ≤ Real.exp ((33299/262144 : ℝ)-(396545477189/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33299/262144 : ℝ) (66599/524288 : ℝ) (396545477189/500000000000 : ℝ) (128431484519/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0527; no trusted numerical premise.
theorem cover8_leaf0527_exp_radius : (998017133810729471/1000000000000000000 : ℝ) ≤ Real.exp ((-8325/524288 : ℝ)/8) ∧ Real.exp ((-8325/524288 : ℝ)/8) ≤ (1949252214474081/1953125000000000 : ℝ) := by
  have h := exp_small_bounds ((-8325/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0527_exp_lower : (920113571223520679/1000000000000000000 : ℝ) ≤ Real.exp ((-85256365645737/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256365645737/128000000000000 : ℝ)/8) ≤ (23002839280588017/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256365645737/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0527_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451869497/500000000000 : ℝ) ≤ 4*Real.exp (66599/524288 : ℝ)*Real.exp (-mu (radius 8 (8325/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451869497/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8325/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0527_exp_radius
  have hrNumeric : (492123362107/500000000000 : ℝ) ≤ Real.exp (-8325/524288 : ℝ) ∧ Real.exp (-8325/524288 : ℝ) ≤ (196849344843/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492123362107/500000000000 : ℝ) ≤ (radius 8 (8325/65536 : ℝ)) ∧ (radius 8 (8325/65536 : ℝ)) ≤ (196849344843/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8325/65536 : ℝ)) (492123362107/500000000000 : ℝ) (196849344843/200000000000 : ℝ) (176800412533/1000000000000 : ℝ) (8840020627/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8325/65536 : ℝ)) (492123362107/500000000000 : ℝ) (196849344843/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8325/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492123362107/500000000000 : ℝ) (196849344843/200000000000 : ℝ) (992123362107/1000000000000 : ℝ) (248030840527/250000000000 : ℝ) (992092094623/1000000000000 : ℝ) (31002877957/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8325/65536 : ℝ)) 1 (992123362107/1000000000000 : ℝ) (248030840527/250000000000 : ℝ) (992092094623/1000000000000 : ℝ) (31002877957/31250000000 : ℝ) (198421545673/200000000000 : ℝ) (496053864183/500000000000 : ℝ) (992107728241/1000000000000 : ℝ) (992107728243/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8325/65536 : ℝ)) 2 (198421545673/200000000000 : ℝ) (496053864183/500000000000 : ℝ) (992107728241/1000000000000 : ℝ) (992107728243/1000000000000 : ℝ) (992107728303/1000000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8325/65536 : ℝ)) 3 (992107728303/1000000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8325/65536 : ℝ)) 4 (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8325/65536 : ℝ)) 5 (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8325/65536 : ℝ)) 6 (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8325/65536 : ℝ)) 7 (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8325/65536 : ℝ))) (176800412533/1000000000000 : ℝ) (8840020627/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8325/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176800412533/1000000000000 : ℝ) (8840020627/50000000000 : ℝ) (294200103133/500000000000 : ℝ) (58840020627/100000000000 : ℝ) (420476411387/1000000000000 : ℝ) (105119102849/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8325/65536 : ℝ))) 1 (294200103133/500000000000 : ℝ) (58840020627/100000000000 : ℝ) (420476411387/1000000000000 : ℝ) (105119102849/250000000000 : ℝ) (252219154413/500000000000 : ℝ) (504438308833/1000000000000 : ℝ) (497401655797/1000000000000 : ℝ) (99480331161/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8325/65536 : ℝ))) 2 (252219154413/500000000000 : ℝ) (504438308833/1000000000000 : ℝ) (497401655797/1000000000000 : ℝ) (99480331161/200000000000 : ℝ) (500919982311/1000000000000 : ℝ) (500919982319/1000000000000 : ℝ) (15653363321/31250000000 : ℝ) (12522690657/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8325/65536 : ℝ))) 3 (500919982311/1000000000000 : ℝ) (500919982319/1000000000000 : ℝ) (15653363321/31250000000 : ℝ) (12522690657/25000000000 : ℝ) (500913804291/1000000000000 : ℝ) (5009138043/10000000000 : ℝ) (500913804253/1000000000000 : ℝ) (250456902131/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8325/65536 : ℝ))) 4 (500913804291/1000000000000 : ℝ) (5009138043/10000000000 : ℝ) (500913804253/1000000000000 : ℝ) (250456902131/500000000000 : ℝ) (31307112767/62500000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8325/65536 : ℝ))) 5 (31307112767/62500000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8325/65536 : ℝ))) 6 (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8325/65536 : ℝ))) 7 (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8325/65536 : ℝ)) hmem 8 (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8325/65536 : ℝ))) hcmem 8 (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8325/65536 : ℝ)) (496053864151/500000000000 : ℝ) (198421545661/200000000000 : ℝ) (500913804271/1000000000000 : ℝ) (500913804281/1000000000000 : ℝ) (99136608523/125000000000 : ℝ) (198273217051/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0527_exp_lower
  have heNumeric : (1027451869497/500000000000 : ℝ)/4 ≤ Real.exp (-85256365645737/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451869497/500000000000 : ℝ)/4 ≤ Real.exp ((66599/524288 : ℝ)-(198273217051/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66599/524288 : ℝ) (8325/65536 : ℝ) (198273217051/250000000000 : ℝ) (1027451869497/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0528; no trusted numerical premise.
theorem cover8_leaf0528_exp_radius : (124752138008437693/125000000000000000 : ℝ) ≤ Real.exp ((-66601/4194304 : ℝ)/8) ∧ Real.exp ((-66601/4194304 : ℝ)/8) ≤ (199603420813500309/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66601/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0528_exp_lower : (920113570481981923/1000000000000000000 : ℝ) ≤ Real.exp ((-85256366471/128000000000 : ℝ)/8) ∧ Real.exp ((-85256366471/128000000000 : ℝ)/8) ≤ (230028392620495481/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256366471/128000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0528_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980745149/200000000000 : ℝ) ≤ 4*Real.exp (8325/65536 : ℝ)*Real.exp (-mu (radius 8 (66601/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980745149/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66601/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0528_exp_radius
  have hrNumeric : (61515405597/62500000000 : ℝ) ≤ Real.exp (-66601/4194304 : ℝ) ∧ Real.exp (-66601/4194304 : ℝ) ≤ (984246489553/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61515405597/62500000000 : ℝ) ≤ (radius 8 (66601/524288 : ℝ)) ∧ (radius 8 (66601/524288 : ℝ)) ≤ (984246489553/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66601/524288 : ℝ)) (61515405597/62500000000 : ℝ) (984246489553/1000000000000 : ℝ) (17680171889/100000000000 : ℝ) (11050107431/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66601/524288 : ℝ)) (61515405597/62500000000 : ℝ) (984246489553/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66601/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61515405597/62500000000 : ℝ) (984246489553/1000000000000 : ℝ) (124015405597/125000000000 : ℝ) (992123244777/1000000000000 : ℝ) (992091976357/1000000000000 : ℝ) (496045988179/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66601/524288 : ℝ)) 1 (124015405597/125000000000 : ℝ) (992123244777/1000000000000 : ℝ) (992091976357/1000000000000 : ℝ) (496045988179/500000000000 : ℝ) (496053805283/500000000000 : ℝ) (124013451321/125000000000 : ℝ) (992107610443/1000000000000 : ℝ) (198421522089/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66601/524288 : ℝ)) 2 (496053805283/500000000000 : ℝ) (124013451321/125000000000 : ℝ) (992107610443/1000000000000 : ℝ) (198421522089/200000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66601/524288 : ℝ)) 3 (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66601/524288 : ℝ)) 4 (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66601/524288 : ℝ)) 5 (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66601/524288 : ℝ)) 6 (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66601/524288 : ℝ)) 7 (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66601/524288 : ℝ))) (17680171889/100000000000 : ℝ) (11050107431/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66601/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17680171889/100000000000 : ℝ) (11050107431/62500000000 : ℝ) (117680171889/200000000000 : ℝ) (73550107431/125000000000 : ℝ) (420477964809/1000000000000 : ℝ) (420477964817/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66601/524288 : ℝ))) 1 (117680171889/200000000000 : ℝ) (73550107431/125000000000 : ℝ) (420477964809/1000000000000 : ℝ) (420477964817/1000000000000 : ℝ) (504439412127/1000000000000 : ℝ) (504439412133/1000000000000 : ℝ) (248701425343/500000000000 : ℝ) (497402850693/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66601/524288 : ℝ))) 2 (504439412127/1000000000000 : ℝ) (504439412133/1000000000000 : ℝ) (248701425343/500000000000 : ℝ) (497402850693/1000000000000 : ℝ) (250460565703/500000000000 : ℝ) (500921131413/1000000000000 : ℝ) (500908775717/1000000000000 : ℝ) (125227193931/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66601/524288 : ℝ))) 3 (250460565703/500000000000 : ℝ) (500921131413/1000000000000 : ℝ) (500908775717/1000000000000 : ℝ) (125227193931/250000000000 : ℝ) (500914953561/1000000000000 : ℝ) (500914953569/1000000000000 : ℝ) (500914953523/1000000000000 : ℝ) (500914953531/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66601/524288 : ℝ))) 4 (500914953561/1000000000000 : ℝ) (500914953569/1000000000000 : ℝ) (500914953523/1000000000000 : ℝ) (500914953531/1000000000000 : ℝ) (250457476771/500000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66601/524288 : ℝ))) 5 (250457476771/500000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66601/524288 : ℝ))) 6 (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66601/524288 : ℝ))) 7 (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66601/524288 : ℝ)) hmem 8 (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66601/524288 : ℝ))) hcmem 8 (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66601/524288 : ℝ)) (124013451313/125000000000 : ℝ) (992107610507/1000000000000 : ℝ) (500914953541/1000000000000 : ℝ) (10018299071/20000000000 : ℝ) (793094781983/1000000000000 : ℝ) (396547391/500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0528_exp_lower
  have heNumeric : (410980745149/200000000000 : ℝ)/4 ≤ Real.exp (-85256366471/128000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980745149/200000000000 : ℝ)/4 ≤ Real.exp ((8325/65536 : ℝ)-(396547391/500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8325/65536 : ℝ) (66601/524288 : ℝ) (396547391/500000000 : ℝ) (410980745149/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0529; no trusted numerical premise.
theorem cover8_leaf0529_exp_radius : (124752134290534313/125000000000000000 : ℝ) ≤ Real.exp ((-33301/2097152 : ℝ)/8) ∧ Real.exp ((-33301/2097152 : ℝ)/8) ≤ (199603414864854901/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33301/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0529_exp_lower : (920113569741133253/1000000000000000000 : ℝ) ≤ Real.exp ((-17051273459099/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051273459099/25600000000000 : ℝ)/8) ≤ (460056784870566627/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051273459099/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0529_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903712509/1000000000000 : ℝ) ≤ 4*Real.exp (66601/524288 : ℝ)*Real.exp (-mu (radius 8 (33301/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903712509/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33301/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0529_exp_radius
  have hrNumeric : (984246254889/1000000000000 : ℝ) ≤ Real.exp (-33301/2097152 : ℝ) ∧ Real.exp (-33301/2097152 : ℝ) ≤ (98424625489/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984246254889/1000000000000 : ℝ) ≤ (radius 8 (33301/262144 : ℝ)) ∧ (radius 8 (33301/262144 : ℝ)) ≤ (98424625489/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33301/262144 : ℝ)) (984246254889/1000000000000 : ℝ) (98424625489/100000000000 : ℝ) (88401512621/500000000000 : ℝ) (176803025249/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33301/262144 : ℝ)) (984246254889/1000000000000 : ℝ) (98424625489/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33301/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984246254889/1000000000000 : ℝ) (98424625489/100000000000 : ℝ) (248030781861/250000000000 : ℝ) (198424625489/200000000000 : ℝ) (99209185809/100000000000 : ℝ) (992091858091/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33301/262144 : ℝ)) 1 (248030781861/250000000000 : ℝ) (198424625489/200000000000 : ℝ) (99209185809/100000000000 : ℝ) (992091858091/1000000000000 : ℝ) (992107492767/1000000000000 : ℝ) (31003359149/31250000000 : ℝ) (992107492643/1000000000000 : ℝ) (198421498529/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33301/262144 : ℝ)) 2 (992107492767/1000000000000 : ℝ) (31003359149/31250000000 : ℝ) (992107492643/1000000000000 : ℝ) (198421498529/200000000000 : ℝ) (198421498541/200000000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33301/262144 : ℝ)) 3 (198421498541/200000000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33301/262144 : ℝ)) 4 (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33301/262144 : ℝ)) 5 (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33301/262144 : ℝ)) 6 (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33301/262144 : ℝ)) 7 (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33301/262144 : ℝ))) (88401512621/500000000000 : ℝ) (176803025249/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33301/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88401512621/500000000000 : ℝ) (176803025249/1000000000000 : ℝ) (588401512621/1000000000000 : ℝ) (4707212101/8000000000 : ℝ) (420479518219/1000000000000 : ℝ) (105119879557/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33301/262144 : ℝ))) 1 (588401512621/1000000000000 : ℝ) (4707212101/8000000000 : ℝ) (420479518219/1000000000000 : ℝ) (105119879557/250000000000 : ℝ) (25222025771/50000000000 : ℝ) (504440515427/1000000000000 : ℝ) (248702022783/500000000000 : ℝ) (248702022787/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33301/262144 : ℝ))) 2 (25222025771/50000000000 : ℝ) (504440515427/1000000000000 : ℝ) (248702022783/500000000000 : ℝ) (248702022787/500000000000 : ℝ) (500922280493/1000000000000 : ℝ) (500922280501/1000000000000 : ℝ) (500909925153/1000000000000 : ℝ) (250454962581/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33301/262144 : ℝ))) 3 (500922280493/1000000000000 : ℝ) (500922280501/1000000000000 : ℝ) (500909925153/1000000000000 : ℝ) (250454962581/500000000000 : ℝ) (500916102823/1000000000000 : ℝ) (31307256427/62500000000 : ℝ) (3913407053/7812500000 : ℝ) (250458051397/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33301/262144 : ℝ))) 4 (500916102823/1000000000000 : ℝ) (31307256427/62500000000 : ℝ) (3913407053/7812500000 : ℝ) (250458051397/500000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33301/262144 : ℝ))) 5 (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33301/262144 : ℝ))) 6 (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33301/262144 : ℝ))) 7 (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33301/262144 : ℝ)) hmem 8 (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33301/262144 : ℝ))) hcmem 8 (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33301/262144 : ℝ)) (31003359147/31250000000 : ℝ) (992107492707/1000000000000 : ℝ) (500916102803/1000000000000 : ℝ) (500916102813/1000000000000 : ℝ) (79309669577/100000000000 : ℝ) (79309669579/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0529_exp_lower
  have heNumeric : (2054903712509/1000000000000 : ℝ)/4 ≤ Real.exp (-17051273459099/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903712509/1000000000000 : ℝ)/4 ≤ Real.exp ((66601/524288 : ℝ)-(79309669579/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66601/524288 : ℝ) (33301/262144 : ℝ) (79309669579/100000000000 : ℝ) (2054903712509/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0530; no trusted numerical premise.
theorem cover8_leaf0530_exp_radius : (998017044581048349/1000000000000000000 : ℝ) ≤ Real.exp ((-66603/4194304 : ℝ)/8) ∧ Real.exp ((-66603/4194304 : ℝ)/8) ≤ (19960340891620967/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66603/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0530_exp_lower : (92011356900373501/100000000000000000 : ℝ) ≤ Real.exp ((-1705127362323/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705127362323/2560000000000 : ℝ)/8) ≤ (920113569003735011/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705127362323/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0530_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451849667/500000000000 : ℝ) ≤ 4*Real.exp (33301/262144 : ℝ)*Real.exp (-mu (radius 8 (66603/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451849667/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66603/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0530_exp_radius
  have hrNumeric : (984246020227/1000000000000 : ℝ) ≤ Real.exp (-66603/4194304 : ℝ) ∧ Real.exp (-66603/4194304 : ℝ) ≤ (246061505057/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984246020227/1000000000000 : ℝ) ≤ (radius 8 (66603/524288 : ℝ)) ∧ (radius 8 (66603/524288 : ℝ)) ≤ (246061505057/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66603/524288 : ℝ)) (984246020227/1000000000000 : ℝ) (246061505057/250000000000 : ℝ) (176804331579/1000000000000 : ℝ) (88402165793/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66603/524288 : ℝ)) (984246020227/1000000000000 : ℝ) (246061505057/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66603/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984246020227/1000000000000 : ℝ) (246061505057/250000000000 : ℝ) (992123010113/1000000000000 : ℝ) (496061505057/500000000000 : ℝ) (992091739823/1000000000000 : ℝ) (39683669593/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66603/524288 : ℝ)) 1 (992123010113/1000000000000 : ℝ) (496061505057/500000000000 : ℝ) (992091739823/1000000000000 : ℝ) (39683669593/40000000000 : ℝ) (124013421871/125000000000 : ℝ) (99210737497/100000000000 : ℝ) (248026843711/250000000000 : ℝ) (992107374847/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66603/524288 : ℝ)) 2 (124013421871/125000000000 : ℝ) (99210737497/100000000000 : ℝ) (248026843711/250000000000 : ℝ) (992107374847/1000000000000 : ℝ) (496053687453/500000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66603/524288 : ℝ)) 3 (496053687453/500000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66603/524288 : ℝ)) 4 (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66603/524288 : ℝ)) 5 (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66603/524288 : ℝ)) 6 (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66603/524288 : ℝ)) 7 (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66603/524288 : ℝ))) (176804331579/1000000000000 : ℝ) (88402165793/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66603/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176804331579/1000000000000 : ℝ) (88402165793/500000000000 : ℝ) (588402165789/1000000000000 : ℝ) (588402165793/1000000000000 : ℝ) (210240535803/500000000000 : ℝ) (84096214323/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66603/524288 : ℝ))) 1 (588402165789/1000000000000 : ℝ) (588402165793/1000000000000 : ℝ) (210240535803/500000000000 : ℝ) (84096214323/200000000000 : ℝ) (504441618697/1000000000000 : ℝ) (31527601169/62500000000 : ℝ) (497405240429/1000000000000 : ℝ) (497405240437/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66603/524288 : ℝ))) 2 (504441618697/1000000000000 : ℝ) (31527601169/62500000000 : ℝ) (497405240429/1000000000000 : ℝ) (497405240437/1000000000000 : ℝ) (500923429563/1000000000000 : ℝ) (500923429571/1000000000000 : ℝ) (500911074573/1000000000000 : ℝ) (250455537291/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66603/524288 : ℝ))) 3 (500923429563/1000000000000 : ℝ) (500923429571/1000000000000 : ℝ) (500911074573/1000000000000 : ℝ) (250455537291/500000000000 : ℝ) (125229313017/250000000000 : ℝ) (500917252077/1000000000000 : ℝ) (500917252029/1000000000000 : ℝ) (500917252039/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66603/524288 : ℝ))) 4 (125229313017/250000000000 : ℝ) (500917252077/1000000000000 : ℝ) (500917252029/1000000000000 : ℝ) (500917252039/1000000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66603/524288 : ℝ))) 5 (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66603/524288 : ℝ))) 6 (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66603/524288 : ℝ))) 7 (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66603/524288 : ℝ)) hmem 8 (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66603/524288 : ℝ))) hcmem 8 (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66603/524288 : ℝ)) (198421474981/200000000000 : ℝ) (992107374909/1000000000000 : ℝ) (31307328253/62500000000 : ℝ) (250458626029/500000000000 : ℝ) (79309860953/100000000000 : ℝ) (15861972191/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0530_exp_lower
  have heNumeric : (1027451849667/500000000000 : ℝ)/4 ≤ Real.exp (-1705127362323/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451849667/500000000000 : ℝ)/4 ≤ Real.exp ((33301/262144 : ℝ)-(15861972191/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33301/262144 : ℝ) (66603/524288 : ℝ) (15861972191/20000000000 : ℝ) (1027451849667/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0531; no trusted numerical premise.
theorem cover8_leaf0531_exp_radius : (499008507418911541/500000000000000000 : ℝ) ≤ Real.exp ((-16651/1048576 : ℝ)/8) ∧ Real.exp ((-16651/1048576 : ℝ)/8) ≤ (998017014837823083/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16651/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0531_exp_lower : (184022713653589393/200000000000000000 : ℝ) ≤ Real.exp ((-85256368935013/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256368935013/128000000000000 : ℝ)/8) ≤ (460056784133973483/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256368935013/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0531_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725921547/250000000000 : ℝ) ≤ 4*Real.exp (66603/524288 : ℝ)*Real.exp (-mu (radius 8 (16651/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725921547/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16651/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0531_exp_radius
  have hrNumeric : (246061446391/250000000000 : ℝ) ≤ Real.exp (-16651/1048576 : ℝ) ∧ Real.exp (-16651/1048576 : ℝ) ≤ (196849157113/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246061446391/250000000000 : ℝ) ≤ (radius 8 (16651/131072 : ℝ)) ∧ (radius 8 (16651/131072 : ℝ)) ≤ (196849157113/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16651/131072 : ℝ)) (246061446391/250000000000 : ℝ) (196849157113/200000000000 : ℝ) (22100704739/125000000000 : ℝ) (88402818959/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16651/131072 : ℝ)) (246061446391/250000000000 : ℝ) (196849157113/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16651/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246061446391/250000000000 : ℝ) (196849157113/200000000000 : ℝ) (496061446391/500000000000 : ℝ) (992122892783/1000000000000 : ℝ) (992091621557/1000000000000 : ℝ) (496045810779/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16651/131072 : ℝ)) 1 (496061446391/500000000000 : ℝ) (992122892783/1000000000000 : ℝ) (992091621557/1000000000000 : ℝ) (496045810779/500000000000 : ℝ) (992107257169/1000000000000 : ℝ) (992107257171/1000000000000 : ℝ) (496053628523/500000000000 : ℝ) (124013407131/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16651/131072 : ℝ)) 2 (992107257169/1000000000000 : ℝ) (992107257171/1000000000000 : ℝ) (496053628523/500000000000 : ℝ) (124013407131/125000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16651/131072 : ℝ)) 3 (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16651/131072 : ℝ)) 4 (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16651/131072 : ℝ)) 5 (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16651/131072 : ℝ)) 6 (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16651/131072 : ℝ)) 7 (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16651/131072 : ℝ))) (22100704739/125000000000 : ℝ) (88402818959/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16651/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22100704739/125000000000 : ℝ) (88402818959/500000000000 : ℝ) (147100704739/250000000000 : ℝ) (588402818959/1000000000000 : ℝ) (210241312491/500000000000 : ℝ) (42048262499/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16651/131072 : ℝ))) 1 (147100704739/250000000000 : ℝ) (588402818959/1000000000000 : ℝ) (210241312491/500000000000 : ℝ) (42048262499/100000000000 : ℝ) (504442721969/1000000000000 : ℝ) (20177708879/40000000000 : ℝ) (497406435283/1000000000000 : ℝ) (49740643529/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16651/131072 : ℝ))) 2 (504442721969/1000000000000 : ℝ) (20177708879/40000000000 : ℝ) (497406435283/1000000000000 : ℝ) (49740643529/100000000000 : ℝ) (250462289313/500000000000 : ℝ) (500924578633/1000000000000 : ℝ) (250456111993/500000000000 : ℝ) (500912223993/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16651/131072 : ℝ))) 3 (250462289313/500000000000 : ℝ) (500924578633/1000000000000 : ℝ) (250456111993/500000000000 : ℝ) (500912223993/1000000000000 : ℝ) (250459200653/500000000000 : ℝ) (500918401313/1000000000000 : ℝ) (500918401267/1000000000000 : ℝ) (20036736051/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16651/131072 : ℝ))) 4 (250459200653/500000000000 : ℝ) (500918401313/1000000000000 : ℝ) (500918401267/1000000000000 : ℝ) (20036736051/40000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16651/131072 : ℝ))) 5 (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16651/131072 : ℝ))) 6 (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16651/131072 : ℝ))) 7 (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16651/131072 : ℝ)) hmem 8 (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16651/131072 : ℝ))) hcmem 8 (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16651/131072 : ℝ)) (992107257107/1000000000000 : ℝ) (99210725711/100000000000 : ℝ) (250459200643/500000000000 : ℝ) (250459200647/500000000000 : ℝ) (9913756541/12500000000 : ℝ) (24784391353/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0531_exp_lower
  have heNumeric : (513725921547/250000000000 : ℝ)/4 ≤ Real.exp (-85256368935013/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725921547/250000000000 : ℝ)/4 ≤ Real.exp ((66603/524288 : ℝ)-(24784391353/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66603/524288 : ℝ) (16651/131072 : ℝ) (24784391353/31250000000 : ℝ) (513725921547/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0532; no trusted numerical premise.
theorem cover8_leaf0532_exp_radius : (9980169850945987/10000000000000000 : ℝ) ≤ Real.exp ((-66605/4194304 : ℝ)/8) ∧ Real.exp ((-66605/4194304 : ℝ)/8) ≤ (998016985094598701/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66605/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0532_exp_lower : (920113567534919263/1000000000000000000 : ℝ) ≤ Real.exp ((-21314092437701/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314092437701/32000000000000 : ℝ)/8) ≤ (28753548985466227/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314092437701/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0532_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903673091/1000000000000 : ℝ) ≤ 4*Real.exp (16651/131072 : ℝ)*Real.exp (-mu (radius 8 (66605/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903673091/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66605/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0532_exp_radius
  have hrNumeric : (492122775451/500000000000 : ℝ) ≤ Real.exp (-66605/4194304 : ℝ) ∧ Real.exp (-66605/4194304 : ℝ) ≤ (984245550903/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492122775451/500000000000 : ℝ) ≤ (radius 8 (66605/524288 : ℝ)) ∧ (radius 8 (66605/524288 : ℝ)) ≤ (984245550903/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66605/524288 : ℝ)) (492122775451/500000000000 : ℝ) (984245550903/1000000000000 : ℝ) (176806944229/1000000000000 : ℝ) (35361388847/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66605/524288 : ℝ)) (492122775451/500000000000 : ℝ) (984245550903/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66605/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492122775451/500000000000 : ℝ) (984245550903/1000000000000 : ℝ) (992122775451/1000000000000 : ℝ) (248030693863/250000000000 : ℝ) (99209150329/100000000000 : ℝ) (248022875823/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66605/524288 : ℝ)) 1 (992122775451/1000000000000 : ℝ) (248030693863/250000000000 : ℝ) (99209150329/100000000000 : ℝ) (248022875823/250000000000 : ℝ) (99210713937/100000000000 : ℝ) (248026784843/250000000000 : ℝ) (992107139247/1000000000000 : ℝ) (992107139249/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66605/524288 : ℝ)) 2 (99210713937/100000000000 : ℝ) (248026784843/250000000000 : ℝ) (992107139247/1000000000000 : ℝ) (992107139249/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66605/524288 : ℝ)) 3 (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66605/524288 : ℝ)) 4 (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66605/524288 : ℝ)) 5 (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66605/524288 : ℝ)) 6 (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66605/524288 : ℝ)) 7 (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66605/524288 : ℝ))) (176806944229/1000000000000 : ℝ) (35361388847/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66605/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176806944229/1000000000000 : ℝ) (35361388847/200000000000 : ℝ) (294201736057/500000000000 : ℝ) (294201736059/500000000000 : ℝ) (420484178333/1000000000000 : ℝ) (420484178341/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66605/524288 : ℝ))) 1 (294201736057/500000000000 : ℝ) (294201736059/500000000000 : ℝ) (420484178333/1000000000000 : ℝ) (420484178341/1000000000000 : ℝ) (504443825223/1000000000000 : ℝ) (50444382523/100000000000 : ℝ) (248703815059/500000000000 : ℝ) (3979261041/8000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66605/524288 : ℝ))) 2 (504443825223/1000000000000 : ℝ) (50444382523/100000000000 : ℝ) (248703815059/500000000000 : ℝ) (3979261041/8000000000 : ℝ) (50092572767/100000000000 : ℝ) (250462863839/500000000000 : ℝ) (25045668669/50000000000 : ℝ) (125228343347/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66605/524288 : ℝ))) 3 (50092572767/100000000000 : ℝ) (250462863839/500000000000 : ℝ) (25045668669/50000000000 : ℝ) (125228343347/250000000000 : ℝ) (20036782021/40000000000 : ℝ) (500919550533/1000000000000 : ℝ) (250459775243/500000000000 : ℝ) (100183910099/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66605/524288 : ℝ))) 4 (20036782021/40000000000 : ℝ) (500919550533/1000000000000 : ℝ) (250459775243/500000000000 : ℝ) (100183910099/200000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66605/524288 : ℝ))) 5 (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66605/524288 : ℝ))) 6 (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66605/524288 : ℝ))) 7 (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66605/524288 : ℝ)) hmem 8 (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66605/524288 : ℝ))) hcmem 8 (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66605/524288 : ℝ)) (248026784827/250000000000 : ℝ) (992107139311/1000000000000 : ℝ) (100183910101/200000000000 : ℝ) (250459775257/500000000000 : ℝ) (793102437/1000000000 : ℝ) (396551218509/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0532_exp_lower
  have heNumeric : (2054903673091/1000000000000 : ℝ)/4 ≤ Real.exp (-21314092437701/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903673091/1000000000000 : ℝ)/4 ≤ Real.exp ((16651/131072 : ℝ)-(396551218509/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16651/131072 : ℝ) (66605/524288 : ℝ) (396551218509/500000000000 : ℝ) (2054903673091/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0533; no trusted numerical premise.
theorem cover8_leaf0533_exp_radius : (199603391070275041/200000000000000000 : ℝ) ≤ Real.exp ((-33303/2097152 : ℝ)/8) ∧ Real.exp ((-33303/2097152 : ℝ)/8) ≤ (499008477675687603/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33303/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0533_exp_lower : (920113566803156717/1000000000000000000 : ℝ) ≤ Real.exp ((-85256370565187/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256370565187/128000000000000 : ℝ)/8) ≤ (460056783401578359/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256370565187/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0533_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903660017/1000000000000 : ℝ) ≤ 4*Real.exp (66605/524288 : ℝ)*Real.exp (-mu (radius 8 (33303/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903660017/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33303/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0533_exp_radius
  have hrNumeric : (984245316239/1000000000000 : ℝ) ≤ Real.exp (-33303/2097152 : ℝ) ∧ Real.exp (-33303/2097152 : ℝ) ≤ (12303066453/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984245316239/1000000000000 : ℝ) ≤ (radius 8 (33303/262144 : ℝ)) ∧ (radius 8 (33303/262144 : ℝ)) ≤ (12303066453/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33303/262144 : ℝ)) (984245316239/1000000000000 : ℝ) (12303066453/12500000000 : ℝ) (176808250541/1000000000000 : ℝ) (44202062637/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33303/262144 : ℝ)) (984245316239/1000000000000 : ℝ) (12303066453/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33303/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984245316239/1000000000000 : ℝ) (12303066453/12500000000 : ℝ) (992122658119/1000000000000 : ℝ) (24803066453/25000000000 : ℝ) (15501427891/15625000000 : ℝ) (39683655401/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33303/262144 : ℝ)) 1 (992122658119/1000000000000 : ℝ) (24803066453/25000000000 : ℝ) (15501427891/15625000000 : ℝ) (39683655401/40000000000 : ℝ) (992107021571/1000000000000 : ℝ) (992107021573/1000000000000 : ℝ) (124013377681/125000000000 : ℝ) (19842140429/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33303/262144 : ℝ)) 2 (992107021571/1000000000000 : ℝ) (992107021573/1000000000000 : ℝ) (124013377681/125000000000 : ℝ) (19842140429/20000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33303/262144 : ℝ)) 3 (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33303/262144 : ℝ)) 4 (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33303/262144 : ℝ)) 5 (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33303/262144 : ℝ)) 6 (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33303/262144 : ℝ)) 7 (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33303/262144 : ℝ))) (176808250541/1000000000000 : ℝ) (44202062637/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33303/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176808250541/1000000000000 : ℝ) (44202062637/250000000000 : ℝ) (58840412527/100000000000 : ℝ) (294202062637/500000000000 : ℝ) (420485731673/1000000000000 : ℝ) (210242865841/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33303/262144 : ℝ))) 1 (58840412527/100000000000 : ℝ) (294202062637/500000000000 : ℝ) (420485731673/1000000000000 : ℝ) (210242865841/500000000000 : ℝ) (504444928471/1000000000000 : ℝ) (252222464239/500000000000 : ℝ) (99481764989/200000000000 : ℝ) (497408824953/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33303/262144 : ℝ))) 2 (504444928471/1000000000000 : ℝ) (252222464239/500000000000 : ℝ) (99481764989/200000000000 : ℝ) (497408824953/1000000000000 : ℝ) (125231719177/250000000000 : ℝ) (125231719179/250000000000 : ℝ) (31307157673/62500000000 : ℝ) (62614315347/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33303/262144 : ℝ))) 3 (125231719177/250000000000 : ℝ) (125231719179/250000000000 : ℝ) (31307157673/62500000000 : ℝ) (62614315347/125000000000 : ℝ) (250460349869/500000000000 : ℝ) (250460349873/500000000000 : ℝ) (500920699699/1000000000000 : ℝ) (125230174927/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33303/262144 : ℝ))) 4 (250460349869/500000000000 : ℝ) (250460349873/500000000000 : ℝ) (500920699699/1000000000000 : ℝ) (125230174927/250000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33303/262144 : ℝ))) 5 (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33303/262144 : ℝ))) 6 (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33303/262144 : ℝ))) 7 (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33303/262144 : ℝ)) hmem 8 (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33303/262144 : ℝ))) hcmem 8 (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33303/262144 : ℝ)) (992107021509/1000000000000 : ℝ) (124013377689/125000000000 : ℝ) (250460349859/500000000000 : ℝ) (500920699727/1000000000000 : ℝ) (793104350711/1000000000000 : ℝ) (793104350729/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0533_exp_lower
  have heNumeric : (2054903660017/1000000000000 : ℝ)/4 ≤ Real.exp (-85256370565187/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903660017/1000000000000 : ℝ)/4 ≤ Real.exp ((66605/524288 : ℝ)-(793104350729/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66605/524288 : ℝ) (33303/262144 : ℝ) (793104350729/1000000000000 : ℝ) (2054903660017/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0534; no trusted numerical premise.
theorem cover8_leaf0534_exp_radius : (998016925608152597/1000000000000000000 : ℝ) ≤ Real.exp ((-66607/4194304 : ℝ)/8) ∧ Real.exp ((-66607/4194304 : ℝ)/8) ≤ (499008462804076299/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66607/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0534_exp_lower : (460056783037249777/500000000000000000 : ℝ) ≤ Real.exp ((-42628185688057/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628185688057/64000000000000 : ℝ)/8) ≤ (184022713214899911/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628185688057/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0534_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903646999/1000000000000 : ℝ) ≤ 4*Real.exp (33303/262144 : ℝ)*Real.exp (-mu (radius 8 (66607/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903646999/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66607/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0534_exp_radius
  have hrNumeric : (984245081577/1000000000000 : ℝ) ≤ Real.exp (-66607/4194304 : ℝ) ∧ Real.exp (-66607/4194304 : ℝ) ≤ (492122540789/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984245081577/1000000000000 : ℝ) ≤ (radius 8 (66607/524288 : ℝ)) ∧ (radius 8 (66607/524288 : ℝ)) ≤ (492122540789/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66607/524288 : ℝ)) (984245081577/1000000000000 : ℝ) (492122540789/500000000000 : ℝ) (88404778419/500000000000 : ℝ) (35361911369/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66607/524288 : ℝ)) (984245081577/1000000000000 : ℝ) (492122540789/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66607/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984245081577/1000000000000 : ℝ) (492122540789/500000000000 : ℝ) (248030635197/250000000000 : ℝ) (992122540789/1000000000000 : ℝ) (992091266757/1000000000000 : ℝ) (992091266759/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66607/524288 : ℝ)) 1 (248030635197/250000000000 : ℝ) (992122540789/1000000000000 : ℝ) (992091266757/1000000000000 : ℝ) (992091266759/1000000000000 : ℝ) (248026725943/250000000000 : ℝ) (496053451887/500000000000 : ℝ) (992106903649/1000000000000 : ℝ) (992106903651/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66607/524288 : ℝ)) 2 (248026725943/250000000000 : ℝ) (496053451887/500000000000 : ℝ) (992106903649/1000000000000 : ℝ) (992106903651/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66607/524288 : ℝ)) 3 (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66607/524288 : ℝ)) 4 (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66607/524288 : ℝ)) 5 (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66607/524288 : ℝ)) 6 (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66607/524288 : ℝ)) 7 (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66607/524288 : ℝ))) (88404778419/500000000000 : ℝ) (35361911369/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66607/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88404778419/500000000000 : ℝ) (35361911369/200000000000 : ℝ) (588404778419/1000000000000 : ℝ) (588404778423/1000000000000 : ℝ) (420487284989/1000000000000 : ℝ) (420487284999/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66607/524288 : ℝ))) 1 (588404778419/1000000000000 : ℝ) (588404778423/1000000000000 : ℝ) (420487284989/1000000000000 : ℝ) (420487284999/1000000000000 : ℝ) (63055753963/125000000000 : ℝ) (504446031711/1000000000000 : ℝ) (248705009877/500000000000 : ℝ) (248705009881/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66607/524288 : ℝ))) 2 (63055753963/125000000000 : ℝ) (504446031711/1000000000000 : ℝ) (248705009877/500000000000 : ℝ) (248705009881/500000000000 : ℝ) (500928025729/1000000000000 : ℝ) (500928025737/1000000000000 : ℝ) (500915672139/1000000000000 : ℝ) (500915672147/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66607/524288 : ℝ))) 3 (500928025729/1000000000000 : ℝ) (500928025737/1000000000000 : ℝ) (500915672139/1000000000000 : ℝ) (500915672147/1000000000000 : ℝ) (250460924467/500000000000 : ℝ) (250460924471/500000000000 : ℝ) (100184369779/200000000000 : ℝ) (62615231113/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66607/524288 : ℝ))) 4 (250460924467/500000000000 : ℝ) (250460924471/500000000000 : ℝ) (100184369779/200000000000 : ℝ) (62615231113/125000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66607/524288 : ℝ))) 5 (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66607/524288 : ℝ))) 6 (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66607/524288 : ℝ))) 7 (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66607/524288 : ℝ)) hmem 8 (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66607/524288 : ℝ))) hcmem 8 (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66607/524288 : ℝ)) (99210690371/100000000000 : ℝ) (992106903713/1000000000000 : ℝ) (250460924457/500000000000 : ℝ) (500921848923/1000000000000 : ℝ) (198276566099/250000000000 : ℝ) (793106264413/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0534_exp_lower
  have heNumeric : (2054903646999/1000000000000 : ℝ)/4 ≤ Real.exp (-42628185688057/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903646999/1000000000000 : ℝ)/4 ≤ Real.exp ((33303/262144 : ℝ)-(793106264413/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33303/262144 : ℝ) (66607/524288 : ℝ) (793106264413/1000000000000 : ℝ) (2054903646999/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0535; no trusted numerical premise.
theorem cover8_leaf0535_exp_radius : (7984135166919447/8000000000000000 : ℝ) ≤ Real.exp ((-4163/262144 : ℝ)/8) ∧ Real.exp ((-4163/262144 : ℝ)/8) ≤ (249504223966232719/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4163/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0535_exp_lower : (460056782674013831/500000000000000000 : ℝ) ≤ Real.exp ((-85256372184609/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256372184609/128000000000000 : ℝ)/8) ≤ (920113565348027663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256372184609/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0535_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903634019/1000000000000 : ℝ) ≤ 4*Real.exp (66607/524288 : ℝ)*Real.exp (-mu (radius 8 (4163/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903634019/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4163/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0535_exp_radius
  have hrNumeric : (196848969383/200000000000 : ℝ) ≤ Real.exp (-4163/262144 : ℝ) ∧ Real.exp (-4163/262144 : ℝ) ≤ (246061211729/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196848969383/200000000000 : ℝ) ≤ (radius 8 (4163/32768 : ℝ)) ∧ (radius 8 (4163/32768 : ℝ)) ≤ (246061211729/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4163/32768 : ℝ)) (196848969383/200000000000 : ℝ) (246061211729/250000000000 : ℝ) (282897381/1600000000 : ℝ) (44202715783/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4163/32768 : ℝ)) (196848969383/200000000000 : ℝ) (246061211729/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4163/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196848969383/200000000000 : ℝ) (246061211729/250000000000 : ℝ) (992122423457/1000000000000 : ℝ) (496061211729/500000000000 : ℝ) (992091148491/1000000000000 : ℝ) (248022787123/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4163/32768 : ℝ)) 1 (992122423457/1000000000000 : ℝ) (496061211729/500000000000 : ℝ) (992091148491/1000000000000 : ℝ) (248022787123/250000000000 : ℝ) (496053392987/500000000000 : ℝ) (39684271439/40000000000 : ℝ) (19842135717/20000000000 : ℝ) (248026696463/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4163/32768 : ℝ)) 2 (496053392987/500000000000 : ℝ) (39684271439/40000000000 : ℝ) (19842135717/20000000000 : ℝ) (248026696463/250000000000 : ℝ) (124013348239/125000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4163/32768 : ℝ)) 3 (124013348239/125000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4163/32768 : ℝ)) 4 (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4163/32768 : ℝ)) 5 (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4163/32768 : ℝ)) 6 (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4163/32768 : ℝ)) 7 (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4163/32768 : ℝ))) (282897381/1600000000 : ℝ) (44202715783/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4163/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (282897381/1600000000 : ℝ) (44202715783/250000000000 : ℝ) (294202715781/500000000000 : ℝ) (294202715783/500000000000 : ℝ) (26280552393/62500000000 : ℝ) (420488838297/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4163/32768 : ℝ))) 1 (294202715781/500000000000 : ℝ) (294202715783/500000000000 : ℝ) (26280552393/62500000000 : ℝ) (420488838297/1000000000000 : ℝ) (20177885397/40000000000 : ℝ) (126111783733/250000000000 : ℝ) (497411214549/1000000000000 : ℝ) (497411214557/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4163/32768 : ℝ))) 2 (20177885397/40000000000 : ℝ) (126111783733/250000000000 : ℝ) (497411214549/1000000000000 : ℝ) (497411214557/1000000000000 : ℝ) (500929174737/1000000000000 : ℝ) (100185834949/200000000000 : ℝ) (500916821497/1000000000000 : ℝ) (100183364301/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4163/32768 : ℝ))) 3 (500929174737/1000000000000 : ℝ) (100185834949/200000000000 : ℝ) (500916821497/1000000000000 : ℝ) (100183364301/200000000000 : ℝ) (500922998117/1000000000000 : ℝ) (801476797/1600000000 : ℝ) (250461499039/500000000000 : ℝ) (500922998087/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4163/32768 : ℝ))) 4 (500922998117/1000000000000 : ℝ) (801476797/1600000000 : ℝ) (250461499039/500000000000 : ℝ) (500922998087/1000000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4163/32768 : ℝ))) 5 (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4163/32768 : ℝ))) 6 (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4163/32768 : ℝ))) 7 (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4163/32768 : ℝ)) hmem 8 (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4163/32768 : ℝ))) hcmem 8 (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4163/32768 : ℝ)) (992106785911/1000000000000 : ℝ) (496053392957/500000000000 : ℝ) (500922998097/1000000000000 : ℝ) (250461499053/500000000000 : ℝ) (39655408903/50000000000 : ℝ) (396554089039/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0535_exp_lower
  have heNumeric : (2054903634019/1000000000000 : ℝ)/4 ≤ Real.exp (-85256372184609/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903634019/1000000000000 : ℝ)/4 ≤ Real.exp ((66607/524288 : ℝ)-(396554089039/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66607/524288 : ℝ) (4163/32768 : ℝ) (396554089039/500000000000 : ℝ) (2054903634019/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0536; no trusted numerical premise.
theorem cover8_leaf0536_exp_radius : (998016866121710039/1000000000000000000 : ℝ) ≤ Real.exp ((-66609/4194304 : ℝ)/8) ∧ Real.exp ((-66609/4194304 : ℝ)/8) ≤ (24950421653042751/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66609/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0536_exp_lower : (920113564622705913/1000000000000000000 : ℝ) ≤ Real.exp ((-5328523311989/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328523311989/8000000000000 : ℝ)/8) ≤ (460056782311352957/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328523311989/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0536_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745181053/50000000000 : ℝ) ≤ 4*Real.exp (4163/32768 : ℝ)*Real.exp (-mu (radius 8 (66609/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (102745181053/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66609/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0536_exp_radius
  have hrNumeric : (246061153063/250000000000 : ℝ) ≤ Real.exp (-66609/4194304 : ℝ) ∧ Real.exp (-66609/4194304 : ℝ) ≤ (984244612253/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246061153063/250000000000 : ℝ) ≤ (radius 8 (66609/524288 : ℝ)) ∧ (radius 8 (66609/524288 : ℝ)) ≤ (984244612253/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66609/524288 : ℝ)) (246061153063/250000000000 : ℝ) (984244612253/1000000000000 : ℝ) (2762690147/15625000000 : ℝ) (35362433883/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66609/524288 : ℝ)) (246061153063/250000000000 : ℝ) (984244612253/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66609/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246061153063/250000000000 : ℝ) (984244612253/1000000000000 : ℝ) (496061153063/500000000000 : ℝ) (992122306127/1000000000000 : ℝ) (62005689389/62500000000 : ℝ) (496045515113/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66609/524288 : ℝ)) 1 (496061153063/500000000000 : ℝ) (992122306127/1000000000000 : ℝ) (62005689389/62500000000 : ℝ) (496045515113/500000000000 : ℝ) (39684266727/40000000000 : ℝ) (992106668177/1000000000000 : ℝ) (992106668051/1000000000000 : ℝ) (496053334027/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66609/524288 : ℝ)) 2 (39684266727/40000000000 : ℝ) (992106668177/1000000000000 : ℝ) (992106668051/1000000000000 : ℝ) (496053334027/500000000000 : ℝ) (992106668113/1000000000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66609/524288 : ℝ)) 3 (992106668113/1000000000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66609/524288 : ℝ)) 4 (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66609/524288 : ℝ)) 5 (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66609/524288 : ℝ)) 6 (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66609/524288 : ℝ)) 7 (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66609/524288 : ℝ))) (2762690147/15625000000 : ℝ) (35362433883/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66609/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2762690147/15625000000 : ℝ) (35362433883/200000000000 : ℝ) (18387690147/31250000000 : ℝ) (147101521177/250000000000 : ℝ) (52561298947/125000000000 : ℝ) (84098078317/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66609/524288 : ℝ))) 1 (18387690147/31250000000 : ℝ) (147101521177/250000000000 : ℝ) (52561298947/125000000000 : ℝ) (84098078317/200000000000 : ℝ) (25222411907/50000000000 : ℝ) (504448238147/1000000000000 : ℝ) (497412409337/1000000000000 : ℝ) (99482481869/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66609/524288 : ℝ))) 2 (25222411907/50000000000 : ℝ) (504448238147/1000000000000 : ℝ) (497412409337/1000000000000 : ℝ) (99482481869/200000000000 : ℝ) (250465161869/500000000000 : ℝ) (250465161873/500000000000 : ℝ) (15653686589/31250000000 : ℝ) (500917970857/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66609/524288 : ℝ))) 3 (250465161869/500000000000 : ℝ) (250465161873/500000000000 : ℝ) (15653686589/31250000000 : ℝ) (500917970857/1000000000000 : ℝ) (500924147293/1000000000000 : ℝ) (250462073651/500000000000 : ℝ) (250462073627/500000000000 : ℝ) (7826939801/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66609/524288 : ℝ))) 4 (500924147293/1000000000000 : ℝ) (250462073651/500000000000 : ℝ) (250462073627/500000000000 : ℝ) (7826939801/15625000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66609/524288 : ℝ))) 5 (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66609/524288 : ℝ))) 6 (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66609/524288 : ℝ))) 7 (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66609/524288 : ℝ)) hmem 8 (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66609/524288 : ℝ))) hcmem 8 (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66609/524288 : ℝ)) (62006666757/62500000000 : ℝ) (248026667029/250000000000 : ℝ) (500924147273/1000000000000 : ℝ) (500924147283/1000000000000 : ℝ) (793110091713/1000000000000 : ℝ) (793110091733/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0536_exp_lower
  have heNumeric : (102745181053/50000000000 : ℝ)/4 ≤ Real.exp (-5328523311989/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745181053/50000000000 : ℝ)/4 ≤ Real.exp ((4163/32768 : ℝ)-(793110091733/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4163/32768 : ℝ) (66609/524288 : ℝ) (793110091733/1000000000000 : ℝ) (102745181053/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0537; no trusted numerical premise.
theorem cover8_leaf0537_exp_radius : (99801683637849009/100000000000000000 : ℝ) ≤ Real.exp ((-33305/2097152 : ℝ)/8) ∧ Real.exp ((-33305/2097152 : ℝ)/8) ≤ (998016836378490091/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33305/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0537_exp_lower : (230028390975237401/250000000000000000 : ℝ) ≤ Real.exp ((-85256373795071/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256373795071/128000000000000 : ℝ)/8) ≤ (184022712780189921/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256373795071/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0537_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980721633/200000000000 : ℝ) ≤ 4*Real.exp (66609/524288 : ℝ)*Real.exp (-mu (radius 8 (33305/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980721633/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33305/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0537_exp_radius
  have hrNumeric : (98424437759/100000000000 : ℝ) ≤ Real.exp (-33305/2097152 : ℝ) ∧ Real.exp (-33305/2097152 : ℝ) ≤ (984244377591/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98424437759/100000000000 : ℝ) ≤ (radius 8 (33305/262144 : ℝ)) ∧ (radius 8 (33305/262144 : ℝ)) ≤ (984244377591/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33305/262144 : ℝ)) (98424437759/100000000000 : ℝ) (984244377591/1000000000000 : ℝ) (7072539027/40000000000 : ℝ) (88406737841/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33305/262144 : ℝ)) (98424437759/100000000000 : ℝ) (984244377591/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33305/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98424437759/100000000000 : ℝ) (984244377591/1000000000000 : ℝ) (198424437759/200000000000 : ℝ) (248030547199/250000000000 : ℝ) (496045455979/500000000000 : ℝ) (992090911959/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33305/262144 : ℝ)) 1 (198424437759/200000000000 : ℝ) (248030547199/250000000000 : ℝ) (496045455979/500000000000 : ℝ) (992090911959/1000000000000 : ℝ) (124013318797/125000000000 : ℝ) (496053275189/500000000000 : ℝ) (992106550253/1000000000000 : ℝ) (198421310051/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33305/262144 : ℝ)) 2 (124013318797/125000000000 : ℝ) (496053275189/500000000000 : ℝ) (992106550253/1000000000000 : ℝ) (198421310051/200000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33305/262144 : ℝ)) 3 (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33305/262144 : ℝ)) 4 (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33305/262144 : ℝ)) 5 (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33305/262144 : ℝ)) 6 (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33305/262144 : ℝ)) 7 (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33305/262144 : ℝ))) (7072539027/40000000000 : ℝ) (88406737841/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33305/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7072539027/40000000000 : ℝ) (88406737841/500000000000 : ℝ) (588406737837/1000000000000 : ℝ) (588406737841/1000000000000 : ℝ) (420491944839/1000000000000 : ℝ) (26280746553/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33305/262144 : ℝ))) 1 (588406737837/1000000000000 : ℝ) (588406737841/1000000000000 : ℝ) (420491944839/1000000000000 : ℝ) (26280746553/62500000000 : ℝ) (252224670669/500000000000 : ℝ) (100889868269/200000000000 : ℝ) (99482720821/200000000000 : ℝ) (497413604113/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33305/262144 : ℝ))) 2 (252224670669/500000000000 : ℝ) (100889868269/200000000000 : ℝ) (99482720821/200000000000 : ℝ) (497413604113/1000000000000 : ℝ) (500931472721/1000000000000 : ℝ) (500931472729/1000000000000 : ℝ) (500919120181/1000000000000 : ℝ) (500919120189/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33305/262144 : ℝ))) 3 (500931472721/1000000000000 : ℝ) (500931472729/1000000000000 : ℝ) (500919120181/1000000000000 : ℝ) (500919120189/1000000000000 : ℝ) (500925296451/1000000000000 : ℝ) (500925296459/1000000000000 : ℝ) (125231324103/250000000000 : ℝ) (500925296421/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33305/262144 : ℝ))) 4 (500925296451/1000000000000 : ℝ) (500925296459/1000000000000 : ℝ) (125231324103/250000000000 : ℝ) (500925296421/1000000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33305/262144 : ℝ))) 5 (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33305/262144 : ℝ))) 6 (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33305/262144 : ℝ))) 7 (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33305/262144 : ℝ)) hmem 8 (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33305/262144 : ℝ))) hcmem 8 (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33305/262144 : ℝ)) (496053275157/500000000000 : ℝ) (992106550317/1000000000000 : ℝ) (500925296431/1000000000000 : ℝ) (12523132411/25000000000 : ℝ) (793112005339/1000000000000 : ℝ) (793112005357/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0537_exp_lower
  have heNumeric : (410980721633/200000000000 : ℝ)/4 ≤ Real.exp (-85256373795071/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980721633/200000000000 : ℝ)/4 ≤ Real.exp ((66609/524288 : ℝ)-(793112005357/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66609/524288 : ℝ) (33305/262144 : ℝ) (793112005357/1000000000000 : ℝ) (410980721633/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0538; no trusted numerical premise.
theorem cover8_leaf0538_exp_radius : (998016806635271027/1000000000000000000 : ℝ) ≤ Real.exp ((-66611/4194304 : ℝ)/8) ∧ Real.exp ((-66611/4194304 : ℝ)/8) ≤ (249504201658817757/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66611/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0538_exp_lower : (920113563180918509/1000000000000000000 : ℝ) ≤ Real.exp ((-42628187298199/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628187298199/64000000000000 : ℝ)/8) ≤ (92011356318091851/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628187298199/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0538_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903595301/1000000000000 : ℝ) ≤ 4*Real.exp (33305/262144 : ℝ)*Real.exp (-mu (radius 8 (66611/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903595301/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66611/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0538_exp_radius
  have hrNumeric : (61515258933/62500000000 : ℝ) ≤ Real.exp (-66611/4194304 : ℝ) ∧ Real.exp (-66611/4194304 : ℝ) ≤ (984244142929/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61515258933/62500000000 : ℝ) ≤ (radius 8 (66611/524288 : ℝ)) ∧ (radius 8 (66611/524288 : ℝ)) ≤ (984244142929/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66611/524288 : ℝ)) (61515258933/62500000000 : ℝ) (984244142929/1000000000000 : ℝ) (44203695483/250000000000 : ℝ) (176814781939/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66611/524288 : ℝ)) (61515258933/62500000000 : ℝ) (984244142929/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66611/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61515258933/62500000000 : ℝ) (984244142929/1000000000000 : ℝ) (124015258933/125000000000 : ℝ) (198424414293/200000000000 : ℝ) (992090793691/1000000000000 : ℝ) (992090793693/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66611/524288 : ℝ)) 1 (124015258933/125000000000 : ℝ) (198424414293/200000000000 : ℝ) (992090793691/1000000000000 : ℝ) (992090793693/1000000000000 : ℝ) (992106432577/1000000000000 : ℝ) (992106432579/1000000000000 : ℝ) (496053216227/500000000000 : ℝ) (124013304057/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66611/524288 : ℝ)) 2 (992106432577/1000000000000 : ℝ) (992106432579/1000000000000 : ℝ) (496053216227/500000000000 : ℝ) (124013304057/125000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66611/524288 : ℝ)) 3 (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66611/524288 : ℝ)) 4 (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66611/524288 : ℝ)) 5 (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66611/524288 : ℝ)) 6 (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66611/524288 : ℝ)) 7 (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66611/524288 : ℝ))) (44203695483/250000000000 : ℝ) (176814781939/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66611/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44203695483/250000000000 : ℝ) (176814781939/1000000000000 : ℝ) (294203695483/500000000000 : ℝ) (58840739097/100000000000 : ℝ) (84098699617/200000000000 : ℝ) (210246749047/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66611/524288 : ℝ))) 1 (294203695483/500000000000 : ℝ) (58840739097/100000000000 : ℝ) (84098699617/200000000000 : ℝ) (210246749047/500000000000 : ℝ) (20178017781/40000000000 : ℝ) (126112611133/250000000000 : ℝ) (497414798861/1000000000000 : ℝ) (497414798869/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66611/524288 : ℝ))) 2 (20178017781/40000000000 : ℝ) (126112611133/250000000000 : ℝ) (497414798861/1000000000000 : ℝ) (497414798869/1000000000000 : ℝ) (500932621693/1000000000000 : ℝ) (500932621701/1000000000000 : ℝ) (250460134751/500000000000 : ℝ) (500920269511/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66611/524288 : ℝ))) 3 (500932621693/1000000000000 : ℝ) (500932621701/1000000000000 : ℝ) (250460134751/500000000000 : ℝ) (500920269511/1000000000000 : ℝ) (500926445597/1000000000000 : ℝ) (250463222803/500000000000 : ℝ) (500926445559/1000000000000 : ℝ) (244592991/488281250 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66611/524288 : ℝ))) 4 (500926445597/1000000000000 : ℝ) (250463222803/500000000000 : ℝ) (500926445559/1000000000000 : ℝ) (244592991/488281250 : ℝ) (250463222789/500000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66611/524288 : ℝ))) 5 (250463222789/500000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66611/524288 : ℝ))) 6 (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66611/524288 : ℝ))) 7 (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66611/524288 : ℝ)) hmem 8 (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66611/524288 : ℝ))) hcmem 8 (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66611/524288 : ℝ)) (198421286503/200000000000 : ℝ) (496053216259/500000000000 : ℝ) (500926445577/1000000000000 : ℝ) (500926445587/1000000000000 : ℝ) (396556959473/500000000000 : ℝ) (396556959483/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0538_exp_lower
  have heNumeric : (2054903595301/1000000000000 : ℝ)/4 ≤ Real.exp (-42628187298199/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903595301/1000000000000 : ℝ)/4 ≤ Real.exp ((33305/262144 : ℝ)-(396556959483/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33305/262144 : ℝ) (66611/524288 : ℝ) (396556959483/500000000000 : ℝ) (2054903595301/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0539; no trusted numerical premise.
theorem cover8_leaf0539_exp_radius : (19960335537841057/20000000000000000 : ℝ) ≤ Real.exp ((-16653/1048576 : ℝ)/8) ∧ Real.exp ((-16653/1048576 : ℝ)/8) ≤ (998016776892052851/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16653/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0539_exp_lower : (920113562463302713/1000000000000000000 : ℝ) ≤ Real.exp ((-85256375395037/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256375395037/128000000000000 : ℝ)/8) ≤ (460056781231651357/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256375395037/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0539_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903582479/1000000000000 : ℝ) ≤ 4*Real.exp (66611/524288 : ℝ)*Real.exp (-mu (radius 8 (16653/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903582479/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16653/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0539_exp_radius
  have hrNumeric : (492121954133/500000000000 : ℝ) ≤ Real.exp (-16653/1048576 : ℝ) ∧ Real.exp (-16653/1048576 : ℝ) ≤ (984243908267/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492121954133/500000000000 : ℝ) ≤ (radius 8 (16653/131072 : ℝ)) ∧ (radius 8 (16653/131072 : ℝ)) ≤ (984243908267/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16653/131072 : ℝ)) (492121954133/500000000000 : ℝ) (984243908267/1000000000000 : ℝ) (8840804409/50000000000 : ℝ) (88408044093/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16653/131072 : ℝ)) (492121954133/500000000000 : ℝ) (984243908267/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16653/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492121954133/500000000000 : ℝ) (984243908267/1000000000000 : ℝ) (992121954133/1000000000000 : ℝ) (496060977067/500000000000 : ℝ) (39683627017/40000000000 : ℝ) (496045337713/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16653/131072 : ℝ)) 1 (992121954133/1000000000000 : ℝ) (496060977067/500000000000 : ℝ) (39683627017/40000000000 : ℝ) (496045337713/500000000000 : ℝ) (992106314779/1000000000000 : ℝ) (49605315739/50000000000 : ℝ) (198421262931/200000000000 : ℝ) (992106314657/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16653/131072 : ℝ)) 2 (992106314779/1000000000000 : ℝ) (49605315739/50000000000 : ℝ) (198421262931/200000000000 : ℝ) (992106314657/1000000000000 : ℝ) (992106314717/1000000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16653/131072 : ℝ)) 3 (992106314717/1000000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16653/131072 : ℝ)) 4 (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16653/131072 : ℝ)) 5 (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16653/131072 : ℝ)) 6 (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16653/131072 : ℝ)) 7 (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16653/131072 : ℝ))) (8840804409/50000000000 : ℝ) (88408044093/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16653/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8840804409/50000000000 : ℝ) (88408044093/500000000000 : ℝ) (58840804409/100000000000 : ℝ) (588408044093/1000000000000 : ℝ) (210247525657/500000000000 : ℝ) (210247525661/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16653/131072 : ℝ))) 1 (58840804409/100000000000 : ℝ) (588408044093/1000000000000 : ℝ) (210247525657/500000000000 : ℝ) (210247525661/500000000000 : ℝ) (252225773851/500000000000 : ℝ) (126112886927/250000000000 : ℝ) (124353998401/250000000000 : ℝ) (497415993611/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16653/131072 : ℝ))) 2 (252225773851/500000000000 : ℝ) (126112886927/250000000000 : ℝ) (124353998401/250000000000 : ℝ) (497415993611/1000000000000 : ℝ) (500933770653/1000000000000 : ℝ) (25046688533/50000000000 : ℝ) (125230354703/250000000000 : ℝ) (25046070941/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16653/131072 : ℝ))) 3 (500933770653/1000000000000 : ℝ) (25046688533/50000000000 : ℝ) (125230354703/250000000000 : ℝ) (25046070941/50000000000 : ℝ) (125231898683/250000000000 : ℝ) (25046379737/50000000000 : ℝ) (250463797347/500000000000 : ℝ) (250463797351/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16653/131072 : ℝ))) 4 (125231898683/250000000000 : ℝ) (25046379737/50000000000 : ℝ) (250463797347/500000000000 : ℝ) (250463797351/500000000000 : ℝ) (500927594713/1000000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16653/131072 : ℝ))) 5 (500927594713/1000000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16653/131072 : ℝ))) 6 (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16653/131072 : ℝ))) 7 (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16653/131072 : ℝ)) hmem 8 (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16653/131072 : ℝ))) hcmem 8 (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16653/131072 : ℝ)) (248026578679/250000000000 : ℝ) (992106314719/1000000000000 : ℝ) (62615949339/125000000000 : ℝ) (500927594721/1000000000000 : ℝ) (793115832537/1000000000000 : ℝ) (396557916277/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0539_exp_lower
  have heNumeric : (2054903582479/1000000000000 : ℝ)/4 ≤ Real.exp (-85256375395037/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903582479/1000000000000 : ℝ)/4 ≤ Real.exp ((66611/524288 : ℝ)-(396557916277/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66611/524288 : ℝ) (16653/131072 : ℝ) (396557916277/500000000000 : ℝ) (2054903582479/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0540; no trusted numerical premise.
theorem cover8_leaf0540_exp_radius : (24950418678720889/25000000000000000 : ℝ) ≤ Real.exp ((-66613/4194304 : ℝ)/8) ∧ Real.exp ((-66613/4194304 : ℝ)/8) ≤ (998016747148835561/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66613/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0540_exp_lower : (460056780873821079/500000000000000000 : ℝ) ≤ Real.exp ((-170512752383/256000000000 : ℝ)/8) ∧ Real.exp ((-170512752383/256000000000 : ℝ)/8) ≤ (920113561747642159/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-170512752383/256000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0540_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903569693/1000000000000 : ℝ) ≤ 4*Real.exp (16653/131072 : ℝ)*Real.exp (-mu (radius 8 (66613/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903569693/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66613/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0540_exp_radius
  have hrNumeric : (246060918401/250000000000 : ℝ) ≤ Real.exp (-66613/4194304 : ℝ) ∧ Real.exp (-66613/4194304 : ℝ) ≤ (196848734721/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246060918401/250000000000 : ℝ) ≤ (radius 8 (66613/524288 : ℝ)) ∧ (radius 8 (66613/524288 : ℝ)) ≤ (196848734721/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66613/524288 : ℝ)) (246060918401/250000000000 : ℝ) (196848734721/200000000000 : ℝ) (176817394417/1000000000000 : ℝ) (176817394423/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66613/524288 : ℝ)) (246060918401/250000000000 : ℝ) (196848734721/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66613/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246060918401/250000000000 : ℝ) (196848734721/200000000000 : ℝ) (496060918401/500000000000 : ℝ) (992121836803/1000000000000 : ℝ) (496045278579/500000000000 : ℝ) (24802263929/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66613/524288 : ℝ)) 1 (496060918401/500000000000 : ℝ) (992121836803/1000000000000 : ℝ) (496045278579/500000000000 : ℝ) (24802263929/25000000000 : ℝ) (49605309849/50000000000 : ℝ) (496053098491/500000000000 : ℝ) (124013274607/125000000000 : ℝ) (992106196859/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66613/524288 : ℝ)) 2 (49605309849/50000000000 : ℝ) (496053098491/500000000000 : ℝ) (124013274607/125000000000 : ℝ) (992106196859/1000000000000 : ℝ) (496053098459/500000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66613/524288 : ℝ)) 3 (496053098459/500000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66613/524288 : ℝ)) 4 (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66613/524288 : ℝ)) 5 (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66613/524288 : ℝ)) 6 (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66613/524288 : ℝ)) 7 (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66613/524288 : ℝ))) (176817394417/1000000000000 : ℝ) (176817394423/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66613/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176817394417/1000000000000 : ℝ) (176817394423/1000000000000 : ℝ) (73551087151/125000000000 : ℝ) (147102174303/250000000000 : ℝ) (105124151131/250000000000 : ℝ) (420496604533/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66613/524288 : ℝ))) 1 (73551087151/125000000000 : ℝ) (147102174303/250000000000 : ℝ) (105124151131/250000000000 : ℝ) (420496604533/1000000000000 : ℝ) (252226325433/500000000000 : ℝ) (504452650873/1000000000000 : ℝ) (124354297083/250000000000 : ℝ) (24870859417/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66613/524288 : ℝ))) 2 (252226325433/500000000000 : ℝ) (504452650873/1000000000000 : ℝ) (124354297083/250000000000 : ℝ) (24870859417/50000000000 : ℝ) (500934919599/1000000000000 : ℝ) (500934919607/1000000000000 : ℝ) (125230642027/250000000000 : ℝ) (125230642029/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66613/524288 : ℝ))) 3 (500934919599/1000000000000 : ℝ) (500934919607/1000000000000 : ℝ) (125230642027/250000000000 : ℝ) (125230642029/250000000000 : ℝ) (500928743853/1000000000000 : ℝ) (250464371931/500000000000 : ℝ) (100185748763/200000000000 : ℝ) (31308046489/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66613/524288 : ℝ))) 4 (500928743853/1000000000000 : ℝ) (250464371931/500000000000 : ℝ) (100185748763/200000000000 : ℝ) (31308046489/62500000000 : ℝ) (250464371917/500000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66613/524288 : ℝ))) 5 (250464371917/500000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66613/524288 : ℝ))) 6 (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66613/524288 : ℝ))) 7 (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66613/524288 : ℝ)) hmem 8 (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66613/524288 : ℝ))) hcmem 8 (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66613/524288 : ℝ)) (992106196917/1000000000000 : ℝ) (992106196921/1000000000000 : ℝ) (500928743833/1000000000000 : ℝ) (500928743843/1000000000000 : ℝ) (158623549221/200000000000 : ℝ) (6344941969/8000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0540_exp_lower
  have heNumeric : (2054903569693/1000000000000 : ℝ)/4 ≤ Real.exp (-170512752383/256000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903569693/1000000000000 : ℝ)/4 ≤ Real.exp ((16653/131072 : ℝ)-(6344941969/8000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16653/131072 : ℝ) (66613/524288 : ℝ) (6344941969/8000000000 : ℝ) (2054903569693/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0541; no trusted numerical premise.
theorem cover8_leaf0541_exp_radius : (249504179351404789/250000000000000000 : ℝ) ≤ Real.exp ((-33307/2097152 : ℝ)/8) ∧ Real.exp ((-33307/2097152 : ℝ)/8) ≤ (998016717405619157/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33307/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0541_exp_lower : (460056780517198451/500000000000000000 : ℝ) ≤ Real.exp ((-3410255079411/5120000000000 : ℝ)/8) ∧ Real.exp ((-3410255079411/5120000000000 : ℝ)/8) ≤ (920113561034396903/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-3410255079411/5120000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0541_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098071139/20000000000 : ℝ) ≤ 4*Real.exp (66613/524288 : ℝ)*Real.exp (-mu (radius 8 (33307/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (41098071139/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33307/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0541_exp_radius
  have hrNumeric : (492121719471/500000000000 : ℝ) ≤ Real.exp (-33307/2097152 : ℝ) ∧ Real.exp (-33307/2097152 : ℝ) ≤ (984243438943/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492121719471/500000000000 : ℝ) ≤ (radius 8 (33307/262144 : ℝ)) ∧ (radius 8 (33307/262144 : ℝ)) ≤ (984243438943/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33307/262144 : ℝ)) (492121719471/500000000000 : ℝ) (984243438943/1000000000000 : ℝ) (44204675161/250000000000 : ℝ) (176818700651/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33307/262144 : ℝ)) (492121719471/500000000000 : ℝ) (984243438943/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33307/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492121719471/500000000000 : ℝ) (984243438943/1000000000000 : ℝ) (992121719471/1000000000000 : ℝ) (62007607467/62500000000 : ℝ) (248022609723/250000000000 : ℝ) (496045219447/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33307/262144 : ℝ)) 1 (992121719471/1000000000000 : ℝ) (62007607467/62500000000 : ℝ) (248022609723/250000000000 : ℝ) (496045219447/500000000000 : ℝ) (992106079181/1000000000000 : ℝ) (992106079183/1000000000000 : ℝ) (496053039529/500000000000 : ℝ) (49605303953/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33307/262144 : ℝ)) 2 (992106079181/1000000000000 : ℝ) (992106079183/1000000000000 : ℝ) (496053039529/500000000000 : ℝ) (49605303953/50000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33307/262144 : ℝ)) 3 (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33307/262144 : ℝ)) 4 (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33307/262144 : ℝ)) 5 (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33307/262144 : ℝ)) 6 (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33307/262144 : ℝ)) 7 (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33307/262144 : ℝ))) (44204675161/250000000000 : ℝ) (176818700651/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33307/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44204675161/250000000000 : ℝ) (176818700651/1000000000000 : ℝ) (294204675161/500000000000 : ℝ) (294204675163/500000000000 : ℝ) (420498157717/1000000000000 : ℝ) (420498157727/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33307/262144 : ℝ))) 1 (294204675161/500000000000 : ℝ) (294204675163/500000000000 : ℝ) (420498157717/1000000000000 : ℝ) (420498157727/1000000000000 : ℝ) (504453754019/1000000000000 : ℝ) (504453754027/1000000000000 : ℝ) (497418383047/1000000000000 : ℝ) (31088648941/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33307/262144 : ℝ))) 2 (504453754019/1000000000000 : ℝ) (504453754027/1000000000000 : ℝ) (497418383047/1000000000000 : ℝ) (31088648941/62500000000 : ℝ) (500936068533/1000000000000 : ℝ) (250468034271/500000000000 : ℝ) (31307732337/62500000000 : ℝ) (500923717401/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33307/262144 : ℝ))) 3 (500936068533/1000000000000 : ℝ) (250468034271/500000000000 : ℝ) (31307732337/62500000000 : ℝ) (500923717401/1000000000000 : ℝ) (250464946481/500000000000 : ℝ) (125232473243/250000000000 : ℝ) (125232473231/250000000000 : ℝ) (250464946467/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33307/262144 : ℝ))) 4 (250464946481/500000000000 : ℝ) (125232473243/250000000000 : ℝ) (125232473231/250000000000 : ℝ) (250464946467/500000000000 : ℝ) (500929892943/1000000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33307/262144 : ℝ))) 5 (500929892943/1000000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33307/262144 : ℝ))) 6 (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33307/262144 : ℝ))) 7 (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33307/262144 : ℝ)) hmem 8 (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33307/262144 : ℝ))) hcmem 8 (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33307/262144 : ℝ)) (992106079119/1000000000000 : ℝ) (496053039561/500000000000 : ℝ) (250464946471/500000000000 : ℝ) (500929892953/1000000000000 : ℝ) (158623931931/200000000000 : ℝ) (31724786387/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0541_exp_lower
  have heNumeric : (41098071139/20000000000 : ℝ)/4 ≤ Real.exp (-3410255079411/5120000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098071139/20000000000 : ℝ)/4 ≤ Real.exp ((66613/524288 : ℝ)-(31724786387/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66613/524288 : ℝ) (33307/262144 : ℝ) (31724786387/40000000000 : ℝ) (41098071139/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0542; no trusted numerical premise.
theorem cover8_leaf0542_exp_radius : (998016687662403639/1000000000000000000 : ℝ) ≤ Real.exp ((-66615/4194304 : ℝ)/8) ∧ Real.exp ((-66615/4194304 : ℝ)/8) ≤ (24950417191560091/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66615/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0542_exp_lower : (92011356032345193/100000000000000000 : ℝ) ≤ Real.exp ((-8525637777649/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525637777649/12800000000000 : ℝ)/8) ≤ (920113560323451931/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525637777649/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0542_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862943031/125000000000 : ℝ) ≤ 4*Real.exp (33307/262144 : ℝ)*Real.exp (-mu (radius 8 (66615/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862943031/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66615/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0542_exp_radius
  have hrNumeric : (24606080107/25000000000 : ℝ) ≤ Real.exp (-66615/4194304 : ℝ) ∧ Real.exp (-66615/4194304 : ℝ) ≤ (984243204281/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24606080107/25000000000 : ℝ) ≤ (radius 8 (66615/524288 : ℝ)) ∧ (radius 8 (66615/524288 : ℝ)) ≤ (984243204281/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66615/524288 : ℝ)) (24606080107/25000000000 : ℝ) (984243204281/1000000000000 : ℝ) (176820006861/1000000000000 : ℝ) (44205001717/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66615/524288 : ℝ)) (24606080107/25000000000 : ℝ) (984243204281/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66615/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24606080107/25000000000 : ℝ) (984243204281/1000000000000 : ℝ) (49606080107/50000000000 : ℝ) (992121602141/1000000000000 : ℝ) (496045160313/500000000000 : ℝ) (992090320627/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66615/524288 : ℝ)) 1 (49606080107/50000000000 : ℝ) (992121602141/1000000000000 : ℝ) (496045160313/500000000000 : ℝ) (992090320627/1000000000000 : ℝ) (992105961383/1000000000000 : ℝ) (124013245173/125000000000 : ℝ) (992105961259/1000000000000 : ℝ) (992105961261/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66615/524288 : ℝ)) 2 (992105961383/1000000000000 : ℝ) (124013245173/125000000000 : ℝ) (992105961259/1000000000000 : ℝ) (992105961261/1000000000000 : ℝ) (992105961321/1000000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66615/524288 : ℝ)) 3 (992105961321/1000000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66615/524288 : ℝ)) 4 (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66615/524288 : ℝ)) 5 (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66615/524288 : ℝ)) 6 (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66615/524288 : ℝ)) 7 (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66615/524288 : ℝ))) (176820006861/1000000000000 : ℝ) (44205001717/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66615/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176820006861/1000000000000 : ℝ) (44205001717/250000000000 : ℝ) (58841000343/100000000000 : ℝ) (294205001717/500000000000 : ℝ) (105124927723/250000000000 : ℝ) (210249855451/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66615/524288 : ℝ))) 1 (58841000343/100000000000 : ℝ) (294205001717/500000000000 : ℝ) (105124927723/250000000000 : ℝ) (210249855451/500000000000 : ℝ) (504454857161/1000000000000 : ℝ) (31528428573/62500000000 : ℝ) (497419577749/1000000000000 : ℝ) (497419577757/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66615/524288 : ℝ))) 2 (504454857161/1000000000000 : ℝ) (31528428573/62500000000 : ℝ) (497419577749/1000000000000 : ℝ) (497419577757/1000000000000 : ℝ) (100187443491/200000000000 : ℝ) (500937217463/1000000000000 : ℝ) (62615608333/125000000000 : ℝ) (31307804167/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66615/524288 : ℝ))) 3 (100187443491/200000000000 : ℝ) (500937217463/1000000000000 : ℝ) (62615608333/125000000000 : ℝ) (31307804167/62500000000 : ℝ) (500931042059/1000000000000 : ℝ) (125232760517/250000000000 : ℝ) (500931042021/1000000000000 : ℝ) (50093104203/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66615/524288 : ℝ))) 4 (500931042059/1000000000000 : ℝ) (125232760517/250000000000 : ℝ) (500931042021/1000000000000 : ℝ) (50093104203/100000000000 : ℝ) (12523276051/25000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66615/524288 : ℝ))) 5 (12523276051/25000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66615/524288 : ℝ))) 6 (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66615/524288 : ℝ))) 7 (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66615/524288 : ℝ)) hmem 8 (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66615/524288 : ℝ))) hcmem 8 (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66615/524288 : ℝ)) (24802649033/25000000000 : ℝ) (992105961323/1000000000000 : ℝ) (500931042039/1000000000000 : ℝ) (500931042049/1000000000000 : ℝ) (396560786593/500000000000 : ℝ) (158624314641/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0542_exp_lower
  have heNumeric : (256862943031/125000000000 : ℝ)/4 ≤ Real.exp (-8525637777649/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862943031/125000000000 : ℝ)/4 ≤ Real.exp ((33307/262144 : ℝ)-(158624314641/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33307/262144 : ℝ) (66615/524288 : ℝ) (158624314641/200000000000 : ℝ) (256862943031/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0543; no trusted numerical premise.
theorem cover8_leaf0543_exp_radius : (62376041119949313/62500000000000000 : ℝ) ≤ Real.exp ((-8327/524288 : ℝ)/8) ∧ Real.exp ((-8327/524288 : ℝ)/8) ≤ (998016657919189009/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8327/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0543_exp_lower : (4600567798072311/5000000000000000 : ℝ) ≤ Real.exp ((-85256378565529/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256378565529/128000000000000 : ℝ)/8) ≤ (920113559614462201/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256378565529/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0543_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745176579/50000000000 : ℝ) ≤ 4*Real.exp (66615/524288 : ℝ)*Real.exp (-mu (radius 8 (8327/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (102745176579/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8327/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0543_exp_radius
  have hrNumeric : (492121484809/500000000000 : ℝ) ≤ Real.exp (-8327/524288 : ℝ) ∧ Real.exp (-8327/524288 : ℝ) ≤ (984242969619/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492121484809/500000000000 : ℝ) ≤ (radius 8 (8327/65536 : ℝ)) ∧ (radius 8 (8327/65536 : ℝ)) ≤ (984242969619/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8327/65536 : ℝ)) (492121484809/500000000000 : ℝ) (984242969619/1000000000000 : ℝ) (176821313069/1000000000000 : ℝ) (7072852523/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8327/65536 : ℝ)) (492121484809/500000000000 : ℝ) (984242969619/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8327/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492121484809/500000000000 : ℝ) (984242969619/1000000000000 : ℝ) (992121484809/1000000000000 : ℝ) (99212148481/100000000000 : ℝ) (992090202359/1000000000000 : ℝ) (992090202361/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8327/65536 : ℝ)) 1 (992121484809/1000000000000 : ℝ) (99212148481/100000000000 : ℝ) (992090202359/1000000000000 : ℝ) (992090202361/1000000000000 : ℝ) (7750826903/7812500000 : ℝ) (496052921793/500000000000 : ℝ) (49605292173/50000000000 : ℝ) (992105843463/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8327/65536 : ℝ)) 2 (7750826903/7812500000 : ℝ) (496052921793/500000000000 : ℝ) (49605292173/50000000000 : ℝ) (992105843463/1000000000000 : ℝ) (496052921761/500000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8327/65536 : ℝ)) 3 (496052921761/500000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8327/65536 : ℝ)) 4 (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8327/65536 : ℝ)) 5 (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8327/65536 : ℝ)) 6 (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8327/65536 : ℝ)) 7 (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8327/65536 : ℝ))) (176821313069/1000000000000 : ℝ) (7072852523/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8327/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176821313069/1000000000000 : ℝ) (7072852523/40000000000 : ℝ) (294205328267/500000000000 : ℝ) (294205328269/500000000000 : ℝ) (420501264051/1000000000000 : ℝ) (420501264059/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8327/65536 : ℝ))) 1 (294205328267/500000000000 : ℝ) (294205328269/500000000000 : ℝ) (420501264051/1000000000000 : ℝ) (420501264059/1000000000000 : ℝ) (126113990073/250000000000 : ℝ) (504455960299/1000000000000 : ℝ) (248710386219/500000000000 : ℝ) (248710386223/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8327/65536 : ℝ))) 2 (126113990073/250000000000 : ℝ) (504455960299/1000000000000 : ℝ) (248710386219/500000000000 : ℝ) (248710386223/500000000000 : ℝ) (100187673273/200000000000 : ℝ) (500938366373/1000000000000 : ℝ) (500926015923/1000000000000 : ℝ) (125231503983/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8327/65536 : ℝ))) 3 (100187673273/200000000000 : ℝ) (500938366373/1000000000000 : ℝ) (500926015923/1000000000000 : ℝ) (125231503983/250000000000 : ℝ) (62616523893/125000000000 : ℝ) (500932191153/1000000000000 : ℝ) (100186438221/200000000000 : ℝ) (100186438223/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8327/65536 : ℝ))) 4 (62616523893/125000000000 : ℝ) (500932191153/1000000000000 : ℝ) (100186438221/200000000000 : ℝ) (100186438223/200000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8327/65536 : ℝ))) 5 (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8327/65536 : ℝ))) 6 (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8327/65536 : ℝ))) 7 (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8327/65536 : ℝ)) hmem 8 (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8327/65536 : ℝ))) hcmem 8 (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8327/65536 : ℝ)) (992105843521/1000000000000 : ℝ) (39684233741/40000000000 : ℝ) (125233047781/250000000000 : ℝ) (250466095567/500000000000 : ℝ) (396561743349/500000000000 : ℝ) (396561743359/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0543_exp_lower
  have heNumeric : (102745176579/50000000000 : ℝ)/4 ≤ Real.exp (-85256378565529/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745176579/50000000000 : ℝ)/4 ≤ Real.exp ((66615/524288 : ℝ)-(396561743359/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66615/524288 : ℝ) (8327/65536 : ℝ) (396561743359/500000000000 : ℝ) (102745176579/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0544; no trusted numerical premise.
theorem cover8_leaf0544_exp_radius : (31188019630499227/31250000000000000 : ℝ) ≤ Real.exp ((-66617/4194304 : ℝ)/8) ∧ Real.exp ((-66617/4194304 : ℝ)/8) ≤ (199603325635195053/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66617/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0544_exp_lower : (920113558907657741/1000000000000000000 : ℝ) ≤ Real.exp ((-10657047419017/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657047419017/16000000000000 : ℝ)/8) ≤ (460056779453828871/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657047419017/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0544_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862939869/125000000000 : ℝ) ≤ 4*Real.exp (8327/65536 : ℝ)*Real.exp (-mu (radius 8 (66617/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862939869/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66617/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0544_exp_radius
  have hrNumeric : (246060683739/250000000000 : ℝ) ≤ Real.exp (-66617/4194304 : ℝ) ∧ Real.exp (-66617/4194304 : ℝ) ≤ (984242734957/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246060683739/250000000000 : ℝ) ≤ (radius 8 (66617/524288 : ℝ)) ∧ (radius 8 (66617/524288 : ℝ)) ≤ (984242734957/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66617/524288 : ℝ)) (246060683739/250000000000 : ℝ) (984242734957/1000000000000 : ℝ) (88411309633/500000000000 : ℝ) (176822619273/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66617/524288 : ℝ)) (246060683739/250000000000 : ℝ) (984242734957/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66617/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246060683739/250000000000 : ℝ) (984242734957/1000000000000 : ℝ) (496060683739/500000000000 : ℝ) (992121367479/1000000000000 : ℝ) (992090084093/1000000000000 : ℝ) (496045042047/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66617/524288 : ℝ)) 1 (496060683739/500000000000 : ℝ) (992121367479/1000000000000 : ℝ) (992090084093/1000000000000 : ℝ) (496045042047/500000000000 : ℝ) (198421145157/200000000000 : ℝ) (992105725787/1000000000000 : ℝ) (496052862831/500000000000 : ℝ) (31003303927/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66617/524288 : ℝ)) 2 (198421145157/200000000000 : ℝ) (992105725787/1000000000000 : ℝ) (496052862831/500000000000 : ℝ) (31003303927/31250000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66617/524288 : ℝ)) 3 (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66617/524288 : ℝ)) 4 (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66617/524288 : ℝ)) 5 (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66617/524288 : ℝ)) 6 (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66617/524288 : ℝ)) 7 (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66617/524288 : ℝ))) (88411309633/500000000000 : ℝ) (176822619273/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66617/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88411309633/500000000000 : ℝ) (176822619273/1000000000000 : ℝ) (588411309633/1000000000000 : ℝ) (588411309637/1000000000000 : ℝ) (420502817191/1000000000000 : ℝ) (1051257043/2500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66617/524288 : ℝ))) 1 (588411309633/1000000000000 : ℝ) (588411309637/1000000000000 : ℝ) (420502817191/1000000000000 : ℝ) (1051257043/2500000000 : ℝ) (126114265853/250000000000 : ℝ) (504457063419/1000000000000 : ℝ) (248710983557/500000000000 : ℝ) (248710983561/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66617/524288 : ℝ))) 2 (126114265853/250000000000 : ℝ) (504457063419/1000000000000 : ℝ) (248710983557/500000000000 : ℝ) (248710983561/500000000000 : ℝ) (500939515263/1000000000000 : ℝ) (500939515271/1000000000000 : ℝ) (500927165171/1000000000000 : ℝ) (25046358259/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66617/524288 : ℝ))) 3 (500939515263/1000000000000 : ℝ) (500939515271/1000000000000 : ℝ) (500927165171/1000000000000 : ℝ) (25046358259/50000000000 : ℝ) (500933340217/1000000000000 : ℝ) (250466670113/500000000000 : ℝ) (250466670089/500000000000 : ℝ) (125233335047/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66617/524288 : ℝ))) 4 (500933340217/1000000000000 : ℝ) (250466670113/500000000000 : ℝ) (250466670089/500000000000 : ℝ) (125233335047/250000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66617/524288 : ℝ))) 5 (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66617/524288 : ℝ))) 6 (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66617/524288 : ℝ))) 7 (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66617/524288 : ℝ)) hmem 8 (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66617/524288 : ℝ))) hcmem 8 (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66617/524288 : ℝ)) (992105725723/1000000000000 : ℝ) (496052862863/500000000000 : ℝ) (500933340197/1000000000000 : ℝ) (500933340207/1000000000000 : ℝ) (793125400193/1000000000000 : ℝ) (198281350053/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0544_exp_lower
  have heNumeric : (256862939869/125000000000 : ℝ)/4 ≤ Real.exp (-10657047419017/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862939869/125000000000 : ℝ)/4 ≤ Real.exp ((8327/65536 : ℝ)-(198281350053/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8327/65536 : ℝ) (66617/524288 : ℝ) (198281350053/250000000000 : ℝ) (256862939869/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0545; no trusted numerical premise.
theorem cover8_leaf0545_exp_radius : (499008299216381203/500000000000000000 : ℝ) ≤ Real.exp ((-33309/2097152 : ℝ)/8) ∧ Real.exp ((-33309/2097152 : ℝ)/8) ≤ (998016598432762407/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33309/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0545_exp_lower : (11501419477550921/12500000000000000 : ℝ) ≤ Real.exp ((-85256380135159/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256380135159/128000000000000 : ℝ)/8) ≤ (920113558204073681/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256380135159/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0545_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451753191/500000000000 : ℝ) ≤ 4*Real.exp (66617/524288 : ℝ)*Real.exp (-mu (radius 8 (33309/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451753191/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33309/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0545_exp_radius
  have hrNumeric : (196848500059/200000000000 : ℝ) ≤ Real.exp (-33309/2097152 : ℝ) ∧ Real.exp (-33309/2097152 : ℝ) ≤ (123030312537/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196848500059/200000000000 : ℝ) ≤ (radius 8 (33309/262144 : ℝ)) ∧ (radius 8 (33309/262144 : ℝ)) ≤ (123030312537/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33309/262144 : ℝ)) (196848500059/200000000000 : ℝ) (123030312537/125000000000 : ℝ) (22102990681/125000000000 : ℝ) (35364785091/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33309/262144 : ℝ)) (196848500059/200000000000 : ℝ) (123030312537/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33309/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196848500059/200000000000 : ℝ) (123030312537/125000000000 : ℝ) (992121250147/1000000000000 : ℝ) (248030312537/250000000000 : ℝ) (992089965827/1000000000000 : ℝ) (248022491457/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33309/262144 : ℝ)) 1 (992121250147/1000000000000 : ℝ) (248030312537/250000000000 : ℝ) (992089965827/1000000000000 : ℝ) (248022491457/250000000000 : ℝ) (992105607987/1000000000000 : ℝ) (248026401997/250000000000 : ℝ) (992105607863/1000000000000 : ℝ) (198421121573/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33309/262144 : ℝ)) 2 (992105607987/1000000000000 : ℝ) (248026401997/250000000000 : ℝ) (992105607863/1000000000000 : ℝ) (198421121573/200000000000 : ℝ) (39684224317/40000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33309/262144 : ℝ)) 3 (39684224317/40000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33309/262144 : ℝ)) 4 (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33309/262144 : ℝ)) 5 (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33309/262144 : ℝ)) 6 (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33309/262144 : ℝ)) 7 (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33309/262144 : ℝ))) (22102990681/125000000000 : ℝ) (35364785091/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33309/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22102990681/125000000000 : ℝ) (35364785091/200000000000 : ℝ) (147102990681/250000000000 : ℝ) (73551495341/125000000000 : ℝ) (420504370307/1000000000000 : ℝ) (420504370317/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33309/262144 : ℝ))) 1 (147102990681/250000000000 : ℝ) (73551495341/125000000000 : ℝ) (420504370307/1000000000000 : ℝ) (420504370317/1000000000000 : ℝ) (100891633303/200000000000 : ℝ) (504458166523/1000000000000 : ℝ) (497423161771/1000000000000 : ℝ) (497423161779/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33309/262144 : ℝ))) 2 (100891633303/200000000000 : ℝ) (504458166523/1000000000000 : ℝ) (497423161771/1000000000000 : ℝ) (497423161779/1000000000000 : ℝ) (500940664143/1000000000000 : ℝ) (500940664151/1000000000000 : ℝ) (500928314401/1000000000000 : ℝ) (50092831441/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33309/262144 : ℝ))) 3 (500940664143/1000000000000 : ℝ) (500940664151/1000000000000 : ℝ) (500928314401/1000000000000 : ℝ) (50092831441/100000000000 : ℝ) (62616811159/125000000000 : ℝ) (500934489281/1000000000000 : ℝ) (500934489233/1000000000000 : ℝ) (500934489243/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33309/262144 : ℝ))) 4 (62616811159/125000000000 : ℝ) (500934489281/1000000000000 : ℝ) (500934489233/1000000000000 : ℝ) (500934489243/1000000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33309/262144 : ℝ))) 5 (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33309/262144 : ℝ))) 6 (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33309/262144 : ℝ))) 7 (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33309/262144 : ℝ)) hmem 8 (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33309/262144 : ℝ))) hcmem 8 (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33309/262144 : ℝ)) (248026401981/250000000000 : ℝ) (992105607927/1000000000000 : ℝ) (125233622313/250000000000 : ℝ) (250467244631/500000000000 : ℝ) (793127313659/1000000000000 : ℝ) (396563656839/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0545_exp_lower
  have heNumeric : (1027451753191/500000000000 : ℝ)/4 ≤ Real.exp (-85256380135159/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451753191/500000000000 : ℝ)/4 ≤ Real.exp ((66617/524288 : ℝ)-(396563656839/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66617/524288 : ℝ) (33309/262144 : ℝ) (396563656839/500000000000 : ℝ) (1027451753191/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0546; no trusted numerical premise.
theorem cover8_leaf0546_exp_radius : (199603313737910087/200000000000000000 : ℝ) ≤ Real.exp ((-66619/4194304 : ℝ)/8) ∧ Real.exp ((-66619/4194304 : ℝ)/8) ≤ (249504142172387609/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66619/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0546_exp_lower : (36804542300070191/40000000000000000 : ℝ) ≤ Real.exp ((-42628190458387/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628190458387/64000000000000 : ℝ)/8) ≤ (115014194687719347/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628190458387/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0546_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451746917/500000000000 : ℝ) ≤ 4*Real.exp (33309/262144 : ℝ)*Real.exp (-mu (radius 8 (66619/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451746917/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66619/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0546_exp_radius
  have hrNumeric : (984242265633/1000000000000 : ℝ) ≤ Real.exp (-66619/4194304 : ℝ) ∧ Real.exp (-66619/4194304 : ℝ) ≤ (492121132817/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984242265633/1000000000000 : ℝ) ≤ (radius 8 (66619/524288 : ℝ)) ∧ (radius 8 (66619/524288 : ℝ)) ≤ (492121132817/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66619/524288 : ℝ)) (984242265633/1000000000000 : ℝ) (492121132817/500000000000 : ℝ) (88412615813/500000000000 : ℝ) (11051576977/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66619/524288 : ℝ)) (984242265633/1000000000000 : ℝ) (492121132817/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66619/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984242265633/1000000000000 : ℝ) (492121132817/500000000000 : ℝ) (62007570801/62500000000 : ℝ) (992121132817/1000000000000 : ℝ) (24802246189/25000000000 : ℝ) (496044923781/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66619/524288 : ℝ)) 1 (62007570801/62500000000 : ℝ) (992121132817/1000000000000 : ℝ) (24802246189/25000000000 : ℝ) (496044923781/500000000000 : ℝ) (248026372547/250000000000 : ℝ) (99210549019/100000000000 : ℝ) (62006593129/62500000000 : ℝ) (992105490067/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66619/524288 : ℝ)) 2 (248026372547/250000000000 : ℝ) (99210549019/100000000000 : ℝ) (62006593129/62500000000 : ℝ) (992105490067/1000000000000 : ℝ) (496052745063/500000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66619/524288 : ℝ)) 3 (496052745063/500000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66619/524288 : ℝ)) 4 (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66619/524288 : ℝ)) 5 (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66619/524288 : ℝ)) 6 (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66619/524288 : ℝ)) 7 (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66619/524288 : ℝ))) (88412615813/500000000000 : ℝ) (11051576977/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66619/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88412615813/500000000000 : ℝ) (11051576977/62500000000 : ℝ) (588412615813/1000000000000 : ℝ) (73551576977/125000000000 : ℝ) (420505923413/1000000000000 : ℝ) (420505923421/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66619/524288 : ℝ))) 1 (588412615813/1000000000000 : ℝ) (73551576977/125000000000 : ℝ) (420505923413/1000000000000 : ℝ) (420505923421/1000000000000 : ℝ) (504459269613/1000000000000 : ℝ) (504459269619/1000000000000 : ℝ) (24871217821/50000000000 : ℝ) (497424356427/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66619/524288 : ℝ))) 2 (504459269613/1000000000000 : ℝ) (504459269619/1000000000000 : ℝ) (24871217821/50000000000 : ℝ) (497424356427/1000000000000 : ℝ) (62617726627/125000000000 : ℝ) (500941813023/1000000000000 : ℝ) (62616182953/125000000000 : ℝ) (31308091477/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66619/524288 : ℝ))) 3 (62617726627/125000000000 : ℝ) (500941813023/1000000000000 : ℝ) (62616182953/125000000000 : ℝ) (31308091477/62500000000 : ℝ) (6261695479/12500000000 : ℝ) (62616954791/125000000000 : ℝ) (500935638281/1000000000000 : ℝ) (50093563829/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66619/524288 : ℝ))) 4 (6261695479/12500000000 : ℝ) (62616954791/125000000000 : ℝ) (500935638281/1000000000000 : ℝ) (50093563829/100000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66619/524288 : ℝ))) 5 (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66619/524288 : ℝ))) 6 (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66619/524288 : ℝ))) 7 (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66619/524288 : ℝ)) hmem 8 (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66619/524288 : ℝ))) hcmem 8 (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66619/524288 : ℝ)) (7936843921/8000000000 : ℝ) (992105490129/1000000000000 : ℝ) (5009356383/10000000000 : ℝ) (500935638309/1000000000000 : ℝ) (396564613557/500000000000 : ℝ) (793129227133/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0546_exp_lower
  have heNumeric : (1027451746917/500000000000 : ℝ)/4 ≤ Real.exp (-42628190458387/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451746917/500000000000 : ℝ)/4 ≤ Real.exp ((33309/262144 : ℝ)-(793129227133/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33309/262144 : ℝ) (66619/524288 : ℝ) (793129227133/1000000000000 : ℝ) (1027451746917/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0547; no trusted numerical premise.
theorem cover8_leaf0547_exp_radius : (998016538946339349/1000000000000000000 : ℝ) ≤ Real.exp ((-16655/1048576 : ℝ)/8) ∧ Real.exp ((-16655/1048576 : ℝ)/8) ≤ (19960330778926787/20000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16655/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0547_exp_lower : (460056778400868077/500000000000000000 : ℝ) ≤ Real.exp ((-85256381695829/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256381695829/128000000000000 : ℝ)/8) ≤ (184022711360347231/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256381695829/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0547_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903481327/1000000000000 : ℝ) ≤ 4*Real.exp (66619/524288 : ℝ)*Real.exp (-mu (radius 8 (16655/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903481327/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16655/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0547_exp_radius
  have hrNumeric : (984242030971/1000000000000 : ℝ) ≤ Real.exp (-16655/1048576 : ℝ) ∧ Real.exp (-16655/1048576 : ℝ) ≤ (246060507743/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984242030971/1000000000000 : ℝ) ≤ (radius 8 (16655/131072 : ℝ)) ∧ (radius 8 (16655/131072 : ℝ)) ≤ (246060507743/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16655/131072 : ℝ)) (984242030971/1000000000000 : ℝ) (246060507743/250000000000 : ℝ) (176826537793/1000000000000 : ℝ) (884132689/5000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16655/131072 : ℝ)) (984242030971/1000000000000 : ℝ) (246060507743/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16655/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984242030971/1000000000000 : ℝ) (246060507743/250000000000 : ℝ) (198424203097/200000000000 : ℝ) (496060507743/500000000000 : ℝ) (496044864647/500000000000 : ℝ) (198417945859/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16655/131072 : ℝ)) 1 (198424203097/200000000000 : ℝ) (496060507743/500000000000 : ℝ) (496044864647/500000000000 : ℝ) (198417945859/200000000000 : ℝ) (992105372389/1000000000000 : ℝ) (992105372391/1000000000000 : ℝ) (496052686133/500000000000 : ℝ) (248026343067/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16655/131072 : ℝ)) 2 (992105372389/1000000000000 : ℝ) (992105372391/1000000000000 : ℝ) (496052686133/500000000000 : ℝ) (248026343067/250000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16655/131072 : ℝ)) 3 (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16655/131072 : ℝ)) 4 (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16655/131072 : ℝ)) 5 (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16655/131072 : ℝ)) 6 (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16655/131072 : ℝ)) 7 (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16655/131072 : ℝ))) (176826537793/1000000000000 : ℝ) (884132689/5000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16655/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176826537793/1000000000000 : ℝ) (884132689/5000000000 : ℝ) (18387914653/31250000000 : ℝ) (5884132689/10000000000 : ℝ) (841014953/2000000000 : ℝ) (42050747651/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16655/131072 : ℝ))) 1 (18387914653/31250000000 : ℝ) (5884132689/10000000000 : ℝ) (841014953/2000000000 : ℝ) (42050747651/100000000000 : ℝ) (252230186349/500000000000 : ℝ) (100892074541/200000000000 : ℝ) (99485110211/200000000000 : ℝ) (497425551063/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16655/131072 : ℝ))) 2 (252230186349/500000000000 : ℝ) (100892074541/200000000000 : ℝ) (99485110211/200000000000 : ℝ) (497425551063/1000000000000 : ℝ) (125235740469/250000000000 : ℝ) (125235740471/250000000000 : ℝ) (250465306417/500000000000 : ℝ) (250465306421/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16655/131072 : ℝ))) 3 (125235740469/250000000000 : ℝ) (125235740471/250000000000 : ℝ) (250465306417/500000000000 : ℝ) (250465306421/500000000000 : ℝ) (100187357471/200000000000 : ℝ) (500936787363/1000000000000 : ℝ) (125234196829/250000000000 : ℝ) (20037471493/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16655/131072 : ℝ))) 4 (100187357471/200000000000 : ℝ) (500936787363/1000000000000 : ℝ) (125234196829/250000000000 : ℝ) (20037471493/40000000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16655/131072 : ℝ))) 5 (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16655/131072 : ℝ))) 6 (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16655/131072 : ℝ))) 7 (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16655/131072 : ℝ)) hmem 8 (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16655/131072 : ℝ))) hcmem 8 (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16655/131072 : ℝ)) (992105372327/1000000000000 : ℝ) (99210537233/100000000000 : ℝ) (100187357467/200000000000 : ℝ) (31308549209/62500000000 : ℝ) (15862622811/20000000000 : ℝ) (99141392571/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0547_exp_lower
  have heNumeric : (2054903481327/1000000000000 : ℝ)/4 ≤ Real.exp (-85256381695829/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903481327/1000000000000 : ℝ)/4 ≤ Real.exp ((66619/524288 : ℝ)-(99141392571/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66619/524288 : ℝ) (16655/131072 : ℝ) (99141392571/125000000000 : ℝ) (2054903481327/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0548; no trusted numerical premise.
theorem cover8_leaf0548_exp_radius : (998016509203129151/1000000000000000000 : ℝ) ≤ Real.exp ((-66621/4194304 : ℝ)/8) ∧ Real.exp ((-66621/4194304 : ℝ)/8) ≤ (15594007956298893/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66621/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0548_exp_lower : (920113556104592889/1000000000000000000 : ℝ) ≤ Real.exp ((-21314095617921/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314095617921/32000000000000 : ℝ)/8) ≤ (92011355610459289/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314095617921/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0548_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903468871/1000000000000 : ℝ) ≤ 4*Real.exp (16655/131072 : ℝ)*Real.exp (-mu (radius 8 (66621/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903468871/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66621/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0548_exp_radius
  have hrNumeric : (98424179631/100000000000 : ℝ) ≤ Real.exp (-66621/4194304 : ℝ) ∧ Real.exp (-66621/4194304 : ℝ) ≤ (984241796311/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98424179631/100000000000 : ℝ) ≤ (radius 8 (66621/524288 : ℝ)) ∧ (radius 8 (66621/524288 : ℝ)) ≤ (984241796311/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66621/524288 : ℝ)) (98424179631/100000000000 : ℝ) (984241796311/1000000000000 : ℝ) (35365568789/200000000000 : ℝ) (11051740247/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66621/524288 : ℝ)) (98424179631/100000000000 : ℝ) (984241796311/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66621/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98424179631/100000000000 : ℝ) (984241796311/1000000000000 : ℝ) (198424179631/200000000000 : ℝ) (248030224539/250000000000 : ℝ) (248022402757/250000000000 : ℝ) (992089611029/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66621/524288 : ℝ)) 1 (198424179631/200000000000 : ℝ) (248030224539/250000000000 : ℝ) (248022402757/250000000000 : ℝ) (992089611029/1000000000000 : ℝ) (992105254591/1000000000000 : ℝ) (992105254593/1000000000000 : ℝ) (248026313617/250000000000 : ℝ) (99210525447/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66621/524288 : ℝ)) 2 (992105254591/1000000000000 : ℝ) (992105254593/1000000000000 : ℝ) (248026313617/250000000000 : ℝ) (99210525447/100000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66621/524288 : ℝ)) 3 (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66621/524288 : ℝ)) 4 (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66621/524288 : ℝ)) 5 (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66621/524288 : ℝ)) 6 (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66621/524288 : ℝ)) 7 (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66621/524288 : ℝ))) (35365568789/200000000000 : ℝ) (11051740247/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66621/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35365568789/200000000000 : ℝ) (11051740247/62500000000 : ℝ) (147103480493/250000000000 : ℝ) (73551740247/125000000000 : ℝ) (105127257391/250000000000 : ℝ) (420509029573/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66621/524288 : ℝ))) 1 (147103480493/250000000000 : ℝ) (73551740247/125000000000 : ℝ) (105127257391/250000000000 : ℝ) (420509029573/1000000000000 : ℝ) (63057684471/125000000000 : ℝ) (20178459031/40000000000 : ℝ) (62178343209/125000000000 : ℝ) (6217834321/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66621/524288 : ℝ))) 2 (63057684471/125000000000 : ℝ) (20178459031/40000000000 : ℝ) (62178343209/125000000000 : ℝ) (6217834321/12500000000 : ℝ) (782725173/1562500000 : ℝ) (62618013841/125000000000 : ℝ) (500931762027/1000000000000 : ℝ) (125232940509/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66621/524288 : ℝ))) 3 (782725173/1562500000 : ℝ) (62618013841/125000000000 : ℝ) (500931762027/1000000000000 : ℝ) (125232940509/250000000000 : ℝ) (500937936373/1000000000000 : ℝ) (250468968191/500000000000 : ℝ) (100187587267/200000000000 : ℝ) (62617242043/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66621/524288 : ℝ))) 4 (500937936373/1000000000000 : ℝ) (250468968191/500000000000 : ℝ) (100187587267/200000000000 : ℝ) (62617242043/125000000000 : ℝ) (250468968177/500000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66621/524288 : ℝ))) 5 (250468968177/500000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66621/524288 : ℝ))) 6 (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66621/524288 : ℝ))) 7 (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66621/524288 : ℝ)) hmem 8 (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66621/524288 : ℝ))) hcmem 8 (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66621/524288 : ℝ)) (992105254529/1000000000000 : ℝ) (248026313633/250000000000 : ℝ) (500937936353/1000000000000 : ℝ) (500937936363/1000000000000 : ℝ) (396566526979/500000000000 : ℝ) (396566526989/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0548_exp_lower
  have heNumeric : (2054903468871/1000000000000 : ℝ)/4 ≤ Real.exp (-21314095617921/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903468871/1000000000000 : ℝ)/4 ≤ Real.exp ((16655/131072 : ℝ)-(396566526989/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16655/131072 : ℝ) (66621/524288 : ℝ) (396566526989/500000000000 : ℝ) (2054903468871/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0549; no trusted numerical premise.
theorem cover8_leaf0549_exp_radius : (499008239729959919/500000000000000000 : ℝ) ≤ Real.exp ((-33311/2097152 : ℝ)/8) ∧ Real.exp ((-33311/2097152 : ℝ)/8) ≤ (998016479459919839/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33311/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0549_exp_lower : (184022711081765959/200000000000000000 : ℝ) ≤ Real.exp ((-85256383246003/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256383246003/128000000000000 : ℝ)/8) ≤ (230028388852207449/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256383246003/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0549_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51372586411/25000000000 : ℝ) ≤ 4*Real.exp (66621/524288 : ℝ)*Real.exp (-mu (radius 8 (33311/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (51372586411/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33311/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0549_exp_radius
  have hrNumeric : (61515097603/62500000000 : ℝ) ≤ Real.exp (-33311/2097152 : ℝ) ∧ Real.exp (-33311/2097152 : ℝ) ≤ (984241561649/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61515097603/62500000000 : ℝ) ≤ (radius 8 (33311/262144 : ℝ)) ∧ (radius 8 (33311/262144 : ℝ)) ≤ (984241561649/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33311/262144 : ℝ)) (61515097603/62500000000 : ℝ) (984241561649/1000000000000 : ℝ) (176829150093/1000000000000 : ℝ) (176829150099/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33311/262144 : ℝ)) (61515097603/62500000000 : ℝ) (984241561649/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33311/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61515097603/62500000000 : ℝ) (984241561649/1000000000000 : ℝ) (124015097603/125000000000 : ℝ) (39684831233/40000000000 : ℝ) (992089492761/1000000000000 : ℝ) (992089492763/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33311/262144 : ℝ)) 1 (124015097603/125000000000 : ℝ) (39684831233/40000000000 : ℝ) (992089492761/1000000000000 : ℝ) (992089492763/1000000000000 : ℝ) (124013142099/125000000000 : ℝ) (496052568397/500000000000 : ℝ) (992105136669/1000000000000 : ℝ) (992105136671/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33311/262144 : ℝ)) 2 (124013142099/125000000000 : ℝ) (496052568397/500000000000 : ℝ) (992105136669/1000000000000 : ℝ) (992105136671/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33311/262144 : ℝ)) 3 (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33311/262144 : ℝ)) 4 (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33311/262144 : ℝ)) 5 (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33311/262144 : ℝ)) 6 (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33311/262144 : ℝ)) 7 (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33311/262144 : ℝ))) (176829150093/1000000000000 : ℝ) (176829150099/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33311/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176829150093/1000000000000 : ℝ) (176829150099/1000000000000 : ℝ) (294207287523/500000000000 : ℝ) (11768291501/20000000000 : ℝ) (420510582617/1000000000000 : ℝ) (3364084661/8000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33311/262144 : ℝ))) 1 (294207287523/500000000000 : ℝ) (11768291501/20000000000 : ℝ) (420510582617/1000000000000 : ℝ) (3364084661/8000000000 : ℝ) (504462578831/1000000000000 : ℝ) (252231289419/500000000000 : ℝ) (497427940281/1000000000000 : ℝ) (497427940289/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33311/262144 : ℝ))) 2 (504462578831/1000000000000 : ℝ) (252231289419/500000000000 : ℝ) (497427940281/1000000000000 : ℝ) (497427940289/1000000000000 : ℝ) (125236314889/250000000000 : ℝ) (125236314891/250000000000 : ℝ) (500932911213/1000000000000 : ℝ) (500932911221/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33311/262144 : ℝ))) 3 (125236314889/250000000000 : ℝ) (125236314891/250000000000 : ℝ) (500932911213/1000000000000 : ℝ) (500932911221/1000000000000 : ℝ) (62617385673/125000000000 : ℝ) (500939085393/1000000000000 : ℝ) (250469542673/500000000000 : ℝ) (100187817071/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33311/262144 : ℝ))) 4 (62617385673/125000000000 : ℝ) (500939085393/1000000000000 : ℝ) (250469542673/500000000000 : ℝ) (100187817071/200000000000 : ℝ) (100187817073/200000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33311/262144 : ℝ))) 5 (100187817073/200000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33311/262144 : ℝ))) 6 (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33311/262144 : ℝ))) 7 (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33311/262144 : ℝ)) hmem 8 (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33311/262144 : ℝ))) hcmem 8 (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33311/262144 : ℝ)) (99210513673/100000000000 : ℝ) (992105136733/1000000000000 : ℝ) (125234771341/250000000000 : ℝ) (250469542687/500000000000 : ℝ) (793134967357/1000000000000 : ℝ) (49570935461/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0549_exp_lower
  have heNumeric : (51372586411/25000000000 : ℝ)/4 ≤ Real.exp (-85256383246003/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51372586411/25000000000 : ℝ)/4 ≤ Real.exp ((66621/524288 : ℝ)-(49570935461/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66621/524288 : ℝ) (33311/262144 : ℝ) (49570935461/62500000000 : ℝ) (51372586411/25000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0525_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0525_certificate
#check SmaleRate.Proofs.cover8_leaf0526_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0526_certificate
#check SmaleRate.Proofs.cover8_leaf0527_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0527_certificate
#check SmaleRate.Proofs.cover8_leaf0528_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0528_certificate
#check SmaleRate.Proofs.cover8_leaf0529_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0529_certificate
#check SmaleRate.Proofs.cover8_leaf0530_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0530_certificate
#check SmaleRate.Proofs.cover8_leaf0531_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0531_certificate
#check SmaleRate.Proofs.cover8_leaf0532_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0532_certificate
#check SmaleRate.Proofs.cover8_leaf0533_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0533_certificate
#check SmaleRate.Proofs.cover8_leaf0534_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0534_certificate
#check SmaleRate.Proofs.cover8_leaf0535_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0535_certificate
#check SmaleRate.Proofs.cover8_leaf0536_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0536_certificate
#check SmaleRate.Proofs.cover8_leaf0537_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0537_certificate
#check SmaleRate.Proofs.cover8_leaf0538_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0538_certificate
#check SmaleRate.Proofs.cover8_leaf0539_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0539_certificate
#check SmaleRate.Proofs.cover8_leaf0540_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0540_certificate
#check SmaleRate.Proofs.cover8_leaf0541_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0541_certificate
#check SmaleRate.Proofs.cover8_leaf0542_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0542_certificate
#check SmaleRate.Proofs.cover8_leaf0543_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0543_certificate
#check SmaleRate.Proofs.cover8_leaf0544_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0544_certificate
#check SmaleRate.Proofs.cover8_leaf0545_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0545_certificate
#check SmaleRate.Proofs.cover8_leaf0546_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0546_certificate
#check SmaleRate.Proofs.cover8_leaf0547_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0547_certificate
#check SmaleRate.Proofs.cover8_leaf0548_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0548_certificate
#check SmaleRate.Proofs.cover8_leaf0549_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0549_certificate
