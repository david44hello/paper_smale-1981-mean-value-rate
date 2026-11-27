/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1300; no trusted numerical premise.
theorem cover8_leaf1300_exp_radius : (124748922063418117/125000000000000000 : ℝ) ≤ Real.exp ((-33733/2097152 : ℝ)/8) ∧ Real.exp ((-33733/2097152 : ℝ)/8) ≤ (997991376507344937/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33733/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1300_exp_lower : (460056771310802381/500000000000000000 : ℝ) ≤ Real.exp ((-10657049684623/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657049684623/16000000000000 : ℝ)/8) ≤ (920113542621604763/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657049684623/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1300_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903227977/1000000000000 : ℝ) ≤ 4*Real.exp (8433/65536 : ℝ)*Real.exp (-mu (radius 8 (33733/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903227977/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33733/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1300_exp_radius
  have hrNumeric : (984043527289/1000000000000 : ℝ) ≤ Real.exp (-33733/2097152 : ℝ) ∧ Real.exp (-33733/2097152 : ℝ) ≤ (98404352729/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984043527289/1000000000000 : ℝ) ≤ (radius 8 (33733/262144 : ℝ)) ∧ (radius 8 (33733/262144 : ℝ)) ≤ (98404352729/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33733/262144 : ℝ)) (984043527289/1000000000000 : ℝ) (98404352729/100000000000 : ℝ) (44481974157/250000000000 : ℝ) (35585579327/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33733/262144 : ℝ)) (984043527289/1000000000000 : ℝ) (98404352729/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33733/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984043527289/1000000000000 : ℝ) (98404352729/100000000000 : ℝ) (248005440911/250000000000 : ℝ) (198404352729/200000000000 : ℝ) (991989681039/1000000000000 : ℝ) (991989681041/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33733/262144 : ℝ)) 1 (248005440911/250000000000 : ℝ) (198404352729/200000000000 : ℝ) (991989681039/1000000000000 : ℝ) (991989681041/1000000000000 : ℝ) (992005722341/1000000000000 : ℝ) (992005722343/1000000000000 : ℝ) (992005722211/1000000000000 : ℝ) (496002861107/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33733/262144 : ℝ)) 2 (992005722341/1000000000000 : ℝ) (992005722343/1000000000000 : ℝ) (992005722211/1000000000000 : ℝ) (496002861107/500000000000 : ℝ) (248001430569/250000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33733/262144 : ℝ)) 3 (248001430569/250000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33733/262144 : ℝ)) 4 (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33733/262144 : ℝ)) 5 (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33733/262144 : ℝ)) 6 (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33733/262144 : ℝ)) 7 (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33733/262144 : ℝ))) (44481974157/250000000000 : ℝ) (35585579327/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33733/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44481974157/250000000000 : ℝ) (35585579327/200000000000 : ℝ) (294481974157/500000000000 : ℝ) (294481974159/500000000000 : ℝ) (13181718839/31250000000 : ℝ) (421815002857/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33733/262144 : ℝ))) 1 (294481974157/500000000000 : ℝ) (294481974159/500000000000 : ℝ) (13181718839/31250000000 : ℝ) (421815002857/1000000000000 : ℝ) (505389475581/1000000000000 : ℝ) (126347368897/250000000000 : ℝ) (124607842233/250000000000 : ℝ) (24921568447/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33733/262144 : ℝ))) 2 (505389475581/1000000000000 : ℝ) (126347368897/250000000000 : ℝ) (124607842233/250000000000 : ℝ) (24921568447/50000000000 : ℝ) (31369401391/62500000000 : ℝ) (62738802783/125000000000 : ℝ) (50189836437/100000000000 : ℝ) (250949182189/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33733/262144 : ℝ))) 3 (31369401391/62500000000 : ℝ) (62738802783/125000000000 : ℝ) (50189836437/100000000000 : ℝ) (250949182189/500000000000 : ℝ) (501904393313/1000000000000 : ℝ) (501904393321/1000000000000 : ℝ) (125476098319/250000000000 : ℝ) (100380878657/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33733/262144 : ℝ))) 4 (501904393313/1000000000000 : ℝ) (501904393321/1000000000000 : ℝ) (125476098319/250000000000 : ℝ) (100380878657/200000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33733/262144 : ℝ))) 5 (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33733/262144 : ℝ))) 6 (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33733/262144 : ℝ))) 7 (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33733/262144 : ℝ)) hmem 8 (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33733/262144 : ℝ))) hcmem 8 (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33733/262144 : ℝ)) (39680228891/40000000000 : ℝ) (992005722279/1000000000000 : ℝ) (250952196647/500000000000 : ℝ) (501904393303/1000000000000 : ℝ) (397371486717/500000000000 : ℝ) (794742973453/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1300_exp_lower
  have heNumeric : (2054903227977/1000000000000 : ℝ)/4 ≤ Real.exp (-10657049684623/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903227977/1000000000000 : ℝ)/4 ≤ Real.exp ((8433/65536 : ℝ)-(794742973453/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8433/65536 : ℝ) (33733/262144 : ℝ) (794742973453/1000000000000 : ℝ) (2054903227977/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1301; no trusted numerical premise.
theorem cover8_leaf1301_exp_radius : (997991317022425223/1000000000000000000 : ℝ) ≤ Real.exp ((-16867/1048576 : ℝ)/8) ∧ Real.exp ((-16867/1048576 : ℝ)/8) ≤ (124748914627803153/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16867/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1301_exp_lower : (460056772490058177/500000000000000000 : ℝ) ≤ Real.exp ((-42628197426091/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628197426091/64000000000000 : ℝ)/8) ≤ (184022708996023271/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628197426091/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1301_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725817529/250000000000 : ℝ) ≤ 4*Real.exp (33733/262144 : ℝ)*Real.exp (-mu (radius 8 (16867/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725817529/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16867/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1301_exp_radius
  have hrNumeric : (984043058061/1000000000000 : ℝ) ≤ Real.exp (-16867/1048576 : ℝ) ∧ Real.exp (-16867/1048576 : ℝ) ≤ (492021529031/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984043058061/1000000000000 : ℝ) ≤ (radius 8 (16867/131072 : ℝ)) ∧ (radius 8 (16867/131072 : ℝ)) ≤ (492021529031/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16867/131072 : ℝ)) (984043058061/1000000000000 : ℝ) (492021529031/500000000000 : ℝ) (177930491709/1000000000000 : ℝ) (44482622929/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16867/131072 : ℝ)) (984043058061/1000000000000 : ℝ) (492021529031/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16867/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984043058061/1000000000000 : ℝ) (492021529031/500000000000 : ℝ) (99202152903/100000000000 : ℝ) (992021529031/1000000000000 : ℝ) (991989444531/1000000000000 : ℝ) (247997361133/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16867/131072 : ℝ)) 1 (99202152903/100000000000 : ℝ) (992021529031/1000000000000 : ℝ) (991989444531/1000000000000 : ℝ) (247997361133/250000000000 : ℝ) (49600274339/50000000000 : ℝ) (496002743391/500000000000 : ℝ) (19840109733/20000000000 : ℝ) (248001371663/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16867/131072 : ℝ)) 2 (49600274339/50000000000 : ℝ) (496002743391/500000000000 : ℝ) (19840109733/20000000000 : ℝ) (248001371663/250000000000 : ℝ) (198401097343/200000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16867/131072 : ℝ)) 3 (198401097343/200000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16867/131072 : ℝ)) 4 (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16867/131072 : ℝ)) 5 (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16867/131072 : ℝ)) 6 (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16867/131072 : ℝ)) 7 (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16867/131072 : ℝ))) (177930491709/1000000000000 : ℝ) (44482622929/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16867/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177930491709/1000000000000 : ℝ) (44482622929/250000000000 : ℝ) (294482622927/500000000000 : ℝ) (294482622929/500000000000 : ℝ) (210909039463/500000000000 : ℝ) (84363615787/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16867/131072 : ℝ))) 1 (294482622927/500000000000 : ℝ) (294482622929/500000000000 : ℝ) (210909039463/500000000000 : ℝ) (84363615787/200000000000 : ℝ) (50539166239/100000000000 : ℝ) (505391662397/1000000000000 : ℝ) (3987469883/8000000000 : ℝ) (498433735383/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16867/131072 : ℝ))) 2 (50539166239/100000000000 : ℝ) (505391662397/1000000000000 : ℝ) (3987469883/8000000000 : ℝ) (498433735383/1000000000000 : ℝ) (250956349441/500000000000 : ℝ) (50191269889/100000000000 : ℝ) (501900641673/1000000000000 : ℝ) (250950320841/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16867/131072 : ℝ))) 3 (250956349441/500000000000 : ℝ) (50191269889/100000000000 : ℝ) (501900641673/1000000000000 : ℝ) (250950320841/500000000000 : ℝ) (501906670277/1000000000000 : ℝ) (250953335143/500000000000 : ℝ) (501906670241/1000000000000 : ℝ) (2007626681/4000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16867/131072 : ℝ))) 4 (501906670277/1000000000000 : ℝ) (250953335143/500000000000 : ℝ) (501906670241/1000000000000 : ℝ) (2007626681/4000000000 : ℝ) (501906670259/1000000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16867/131072 : ℝ))) 5 (501906670259/1000000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16867/131072 : ℝ))) 6 (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16867/131072 : ℝ))) 7 (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16867/131072 : ℝ)) hmem 8 (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16867/131072 : ℝ))) hcmem 8 (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16867/131072 : ℝ)) (496002743357/500000000000 : ℝ) (992005486717/1000000000000 : ℝ) (250953335129/500000000000 : ℝ) (125476667567/250000000000 : ℝ) (6357974141/8000000000 : ℝ) (198686691911/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1301_exp_lower
  have heNumeric : (513725817529/250000000000 : ℝ)/4 ≤ Real.exp (-42628197426091/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725817529/250000000000 : ℝ)/4 ≤ Real.exp ((33733/262144 : ℝ)-(198686691911/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33733/262144 : ℝ) (16867/131072 : ℝ) (198686691911/250000000000 : ℝ) (513725817529/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1302; no trusted numerical premise.
theorem cover8_leaf1302_exp_radius : (15593613399023579/15625000000000000 : ℝ) ≤ Real.exp ((-33735/2097152 : ℝ)/8) ∧ Real.exp ((-33735/2097152 : ℝ)/8) ≤ (997991257537509057/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33735/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1302_exp_lower : (3594193544325211/3906250000000000 : ℝ) ≤ Real.exp ((-4262819610889/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262819610889/6400000000000 : ℝ)/8) ≤ (920113547347254017/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262819610889/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1302_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862914051/125000000000 : ℝ) ≤ 4*Real.exp (16867/131072 : ℝ)*Real.exp (-mu (radius 8 (33735/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862914051/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33735/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1302_exp_radius
  have hrNumeric : (984042588833/1000000000000 : ℝ) ≤ Real.exp (-33735/2097152 : ℝ) ∧ Real.exp (-33735/2097152 : ℝ) ≤ (492021294417/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984042588833/1000000000000 : ℝ) ≤ (radius 8 (33735/262144 : ℝ)) ∧ (radius 8 (33735/262144 : ℝ)) ≤ (492021294417/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33735/262144 : ℝ)) (984042588833/1000000000000 : ℝ) (492021294417/500000000000 : ℝ) (177933086751/1000000000000 : ℝ) (177933086757/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33735/262144 : ℝ)) (984042588833/1000000000000 : ℝ) (492021294417/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33735/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984042588833/1000000000000 : ℝ) (492021294417/500000000000 : ℝ) (62001330901/62500000000 : ℝ) (992021294417/1000000000000 : ℝ) (495994604011/500000000000 : ℝ) (991989208023/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33735/262144 : ℝ)) 1 (62001330901/62500000000 : ℝ) (992021294417/1000000000000 : ℝ) (495994604011/500000000000 : ℝ) (991989208023/1000000000000 : ℝ) (992005251219/1000000000000 : ℝ) (49600262561/50000000000 : ℝ) (992005251089/1000000000000 : ℝ) (992005251091/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33735/262144 : ℝ)) 2 (992005251219/1000000000000 : ℝ) (49600262561/50000000000 : ℝ) (992005251089/1000000000000 : ℝ) (992005251091/1000000000000 : ℝ) (496002625577/500000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33735/262144 : ℝ)) 3 (496002625577/500000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33735/262144 : ℝ)) 4 (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33735/262144 : ℝ)) 5 (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33735/262144 : ℝ)) 6 (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33735/262144 : ℝ)) 7 (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33735/262144 : ℝ))) (177933086751/1000000000000 : ℝ) (177933086757/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33735/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177933086751/1000000000000 : ℝ) (177933086757/1000000000000 : ℝ) (4711732347/8000000000 : ℝ) (588966543379/1000000000000 : ℝ) (84364230987/200000000000 : ℝ) (421821154943/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33735/262144 : ℝ))) 1 (4711732347/8000000000 : ℝ) (588966543379/1000000000000 : ℝ) (84364230987/200000000000 : ℝ) (421821154943/1000000000000 : ℝ) (101078769831/200000000000 : ℝ) (505393849161/1000000000000 : ℝ) (249218050883/500000000000 : ℝ) (249218050887/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33735/262144 : ℝ))) 2 (101078769831/200000000000 : ℝ) (505393849161/1000000000000 : ℝ) (249218050883/500000000000 : ℝ) (249218050887/500000000000 : ℝ) (25095748773/50000000000 : ℝ) (125478743867/250000000000 : ℝ) (31368932433/62500000000 : ℝ) (62737864867/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33735/262144 : ℝ))) 3 (25095748773/50000000000 : ℝ) (125478743867/250000000000 : ℝ) (31368932433/62500000000 : ℝ) (62737864867/125000000000 : ℝ) (250954473597/500000000000 : ℝ) (250954473601/500000000000 : ℝ) (501908947157/1000000000000 : ℝ) (250954473583/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33735/262144 : ℝ))) 4 (250954473597/500000000000 : ℝ) (250954473601/500000000000 : ℝ) (501908947157/1000000000000 : ℝ) (250954473583/500000000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33735/262144 : ℝ))) 5 (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33735/262144 : ℝ))) 6 (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33735/262144 : ℝ))) 7 (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33735/262144 : ℝ)) hmem 8 (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33735/262144 : ℝ))) hcmem 8 (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33735/262144 : ℝ)) (992005251153/1000000000000 : ℝ) (248001312789/250000000000 : ℝ) (20076357887/40000000000 : ℝ) (31369309199/62500000000 : ℝ) (397375280871/500000000000 : ℝ) (4967191011/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1302_exp_lower
  have heNumeric : (256862914051/125000000000 : ℝ)/4 ≤ Real.exp (-4262819610889/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862914051/125000000000 : ℝ)/4 ≤ Real.exp ((16867/131072 : ℝ)-(4967191011/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16867/131072 : ℝ) (33735/262144 : ℝ) (4967191011/6250000000 : ℝ) (256862914051/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1303; no trusted numerical premise.
theorem cover8_leaf1303_exp_radius : (199598239610519287/200000000000000000 : ℝ) ≤ Real.exp ((-4217/262144 : ℝ)/8) ∧ Real.exp ((-4217/262144 : ℝ)/8) ≤ (249497799513149109/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4217/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1303_exp_lower : (920113549722672707/1000000000000000000 : ℝ) ≤ Real.exp ((-42628194787081/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628194787081/64000000000000 : ℝ)/8) ≤ (230028387430668177/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628194787081/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1303_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903354849/1000000000000 : ℝ) ≤ 4*Real.exp (33735/262144 : ℝ)*Real.exp (-mu (radius 8 (4217/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903354849/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4217/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1303_exp_radius
  have hrNumeric : (196808423921/200000000000 : ℝ) ≤ Real.exp (-4217/262144 : ℝ) ∧ Real.exp (-4217/262144 : ℝ) ≤ (492021059803/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196808423921/200000000000 : ℝ) ≤ (radius 8 (4217/32768 : ℝ)) ∧ (radius 8 (4217/32768 : ℝ)) ≤ (492021059803/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4217/32768 : ℝ)) (196808423921/200000000000 : ℝ) (492021059803/500000000000 : ℝ) (88967840877/500000000000 : ℝ) (1112098011/6250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4217/32768 : ℝ)) (196808423921/200000000000 : ℝ) (492021059803/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4217/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196808423921/200000000000 : ℝ) (492021059803/500000000000 : ℝ) (496010529901/500000000000 : ℝ) (992021059803/1000000000000 : ℝ) (991988971513/1000000000000 : ℝ) (198397794303/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4217/32768 : ℝ)) 1 (496010529901/500000000000 : ℝ) (992021059803/1000000000000 : ℝ) (991988971513/1000000000000 : ℝ) (198397794303/200000000000 : ℝ) (992005015657/1000000000000 : ℝ) (992005015659/1000000000000 : ℝ) (992005015527/1000000000000 : ℝ) (99200501553/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4217/32768 : ℝ)) 2 (992005015657/1000000000000 : ℝ) (992005015659/1000000000000 : ℝ) (992005015527/1000000000000 : ℝ) (99200501553/100000000000 : ℝ) (124000626949/125000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4217/32768 : ℝ)) 3 (124000626949/125000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4217/32768 : ℝ)) 4 (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4217/32768 : ℝ)) 5 (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4217/32768 : ℝ)) 6 (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4217/32768 : ℝ)) 7 (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4217/32768 : ℝ))) (88967840877/500000000000 : ℝ) (1112098011/6250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4217/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88967840877/500000000000 : ℝ) (1112098011/6250000000 : ℝ) (588967840877/1000000000000 : ℝ) (7362098011/12500000000 : ℝ) (3374593847/8000000000 : ℝ) (421824230883/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4217/32768 : ℝ))) 1 (588967840877/1000000000000 : ℝ) (7362098011/12500000000 : ℝ) (3374593847/8000000000 : ℝ) (421824230883/1000000000000 : ℝ) (126349008969/250000000000 : ℝ) (252698017941/500000000000 : ℝ) (249219234053/500000000000 : ℝ) (498438468113/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4217/32768 : ℝ))) 2 (126349008969/250000000000 : ℝ) (252698017941/500000000000 : ℝ) (249219234053/500000000000 : ℝ) (498438468113/1000000000000 : ℝ) (501917251991/1000000000000 : ℝ) (250958625999/500000000000 : ℝ) (62738149517/125000000000 : ℝ) (31369074759/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4217/32768 : ℝ))) 3 (501917251991/1000000000000 : ℝ) (250958625999/500000000000 : ℝ) (62738149517/125000000000 : ℝ) (31369074759/62500000000 : ℝ) (501911224063/1000000000000 : ℝ) (501911224071/1000000000000 : ℝ) (501911224027/1000000000000 : ℝ) (100382244807/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4217/32768 : ℝ))) 4 (501911224063/1000000000000 : ℝ) (501911224071/1000000000000 : ℝ) (501911224027/1000000000000 : ℝ) (100382244807/200000000000 : ℝ) (100382244809/200000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4217/32768 : ℝ))) 5 (100382244809/200000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4217/32768 : ℝ))) 6 (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4217/32768 : ℝ))) 7 (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4217/32768 : ℝ)) hmem 8 (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4217/32768 : ℝ))) hcmem 8 (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4217/32768 : ℝ)) (992005015591/1000000000000 : ℝ) (198401003119/200000000000 : ℝ) (125477806011/250000000000 : ℝ) (501911224053/1000000000000 : ℝ) (158950871157/200000000000 : ℝ) (198688588951/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1303_exp_lower
  have heNumeric : (2054903354849/1000000000000 : ℝ)/4 ≤ Real.exp (-42628194787081/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903354849/1000000000000 : ℝ)/4 ≤ Real.exp ((33735/262144 : ℝ)-(198688588951/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33735/262144 : ℝ) (4217/32768 : ℝ) (198688588951/250000000000 : ℝ) (2054903354849/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1304; no trusted numerical premise.
theorem cover8_leaf1304_exp_radius : (498995569283843679/500000000000000000 : ℝ) ≤ Real.exp ((-33737/2097152 : ℝ)/8) ∧ Real.exp ((-33737/2097152 : ℝ)/8) ≤ (997991138567687359/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33737/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1304_exp_lower : (230028388026679367/250000000000000000 : ℝ) ≤ Real.exp ((-5328524182559/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328524182559/8000000000000 : ℝ)/8) ≤ (920113552106717469/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328524182559/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1304_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903397443/1000000000000 : ℝ) ≤ 4*Real.exp (4217/32768 : ℝ)*Real.exp (-mu (radius 8 (33737/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903397443/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33737/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1304_exp_radius
  have hrNumeric : (984041650377/1000000000000 : ℝ) ≤ Real.exp (-33737/2097152 : ℝ) ∧ Real.exp (-33737/2097152 : ℝ) ≤ (492020825189/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984041650377/1000000000000 : ℝ) ≤ (radius 8 (33737/262144 : ℝ)) ∧ (radius 8 (33737/262144 : ℝ)) ≤ (492020825189/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33737/262144 : ℝ)) (984041650377/1000000000000 : ℝ) (492020825189/500000000000 : ℝ) (177938276717/1000000000000 : ℝ) (44484569181/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33737/262144 : ℝ)) (984041650377/1000000000000 : ℝ) (492020825189/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33737/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984041650377/1000000000000 : ℝ) (492020825189/500000000000 : ℝ) (248005206297/250000000000 : ℝ) (992020825189/1000000000000 : ℝ) (198397747001/200000000000 : ℝ) (495994367503/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33737/262144 : ℝ)) 1 (248005206297/250000000000 : ℝ) (992020825189/1000000000000 : ℝ) (198397747001/200000000000 : ℝ) (495994367503/500000000000 : ℝ) (15500074689/15625000000 : ℝ) (496002390049/500000000000 : ℝ) (496002389983/500000000000 : ℝ) (15500074687/15625000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33737/262144 : ℝ)) 2 (15500074689/15625000000 : ℝ) (496002390049/500000000000 : ℝ) (496002389983/500000000000 : ℝ) (15500074687/15625000000 : ℝ) (992004780031/1000000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33737/262144 : ℝ)) 3 (992004780031/1000000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33737/262144 : ℝ)) 4 (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33737/262144 : ℝ)) 5 (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33737/262144 : ℝ)) 6 (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33737/262144 : ℝ)) 7 (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33737/262144 : ℝ))) (177938276717/1000000000000 : ℝ) (44484569181/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33737/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177938276717/1000000000000 : ℝ) (44484569181/250000000000 : ℝ) (294484569179/500000000000 : ℝ) (294484569181/500000000000 : ℝ) (210913653373/500000000000 : ℝ) (84365461351/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33737/262144 : ℝ))) 1 (294484569179/500000000000 : ℝ) (294484569181/500000000000 : ℝ) (210913653373/500000000000 : ℝ) (84365461351/200000000000 : ℝ) (63174777819/125000000000 : ℝ) (505398222559/1000000000000 : ℝ) (62305104299/125000000000 : ℝ) (623051043/1250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33737/262144 : ℝ))) 2 (63174777819/125000000000 : ℝ) (505398222559/1000000000000 : ℝ) (62305104299/125000000000 : ℝ) (623051043/1250000000 : ℝ) (62739941059/125000000000 : ℝ) (3136997053/6250000000 : ℝ) (250953736647/500000000000 : ℝ) (501907473303/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33737/262144 : ℝ))) 3 (62739941059/125000000000 : ℝ) (3136997053/6250000000 : ℝ) (250953736647/500000000000 : ℝ) (501907473303/1000000000000 : ℝ) (501913500883/1000000000000 : ℝ) (125478375223/250000000000 : ℝ) (250956750423/500000000000 : ℝ) (62739187607/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33737/262144 : ℝ))) 4 (501913500883/1000000000000 : ℝ) (125478375223/250000000000 : ℝ) (250956750423/500000000000 : ℝ) (62739187607/125000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33737/262144 : ℝ))) 5 (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33737/262144 : ℝ))) 6 (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33737/262144 : ℝ))) 7 (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33737/262144 : ℝ)) hmem 8 (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33737/262144 : ℝ))) hcmem 8 (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33737/262144 : ℝ)) (99200478003/100000000000 : ℝ) (992004780033/1000000000000 : ℝ) (7842398451/15625000000 : ℝ) (250956750437/500000000000 : ℝ) (794758149753/1000000000000 : ℝ) (794758149773/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1304_exp_lower
  have heNumeric : (2054903397443/1000000000000 : ℝ)/4 ≤ Real.exp (-5328524182559/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903397443/1000000000000 : ℝ)/4 ≤ Real.exp ((4217/32768 : ℝ)-(794758149773/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4217/32768 : ℝ) (33737/262144 : ℝ) (794758149773/1000000000000 : ℝ) (2054903397443/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1305; no trusted numerical premise.
theorem cover8_leaf1305_exp_radius : (249497769770695457/250000000000000000 : ℝ) ≤ Real.exp ((-16869/1048576 : ℝ)/8) ∧ Real.exp ((-16869/1048576 : ℝ)/8) ≤ (997991079082781829/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16869/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1305_exp_lower : (460056777249751657/500000000000000000 : ℝ) ≤ Real.exp ((-42628192128999/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628192128999/64000000000000 : ℝ)/8) ≤ (184022710899900663/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628192128999/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1305_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451720097/500000000000 : ℝ) ≤ 4*Real.exp (33737/262144 : ℝ)*Real.exp (-mu (radius 8 (16869/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451720097/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16869/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1305_exp_radius
  have hrNumeric : (984041181149/1000000000000 : ℝ) ≤ Real.exp (-16869/1048576 : ℝ) ∧ Real.exp (-16869/1048576 : ℝ) ≤ (19680823623/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984041181149/1000000000000 : ℝ) ≤ (radius 8 (16869/131072 : ℝ)) ∧ (radius 8 (16869/131072 : ℝ)) ≤ (19680823623/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16869/131072 : ℝ)) (984041181149/1000000000000 : ℝ) (19680823623/20000000000 : ℝ) (88970435821/500000000000 : ℝ) (177940871649/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16869/131072 : ℝ)) (984041181149/1000000000000 : ℝ) (19680823623/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16869/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984041181149/1000000000000 : ℝ) (19680823623/20000000000 : ℝ) (496010295287/500000000000 : ℝ) (39680823623/40000000000 : ℝ) (15499820289/15625000000 : ℝ) (991988498497/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16869/131072 : ℝ)) 1 (496010295287/500000000000 : ℝ) (39680823623/40000000000 : ℝ) (15499820289/15625000000 : ℝ) (991988498497/1000000000000 : ℝ) (198400908907/200000000000 : ℝ) (124000568067/125000000000 : ℝ) (198400908881/200000000000 : ℝ) (992004544407/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16869/131072 : ℝ)) 2 (198400908907/200000000000 : ℝ) (124000568067/125000000000 : ℝ) (198400908881/200000000000 : ℝ) (992004544407/1000000000000 : ℝ) (99200454447/100000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16869/131072 : ℝ)) 3 (99200454447/100000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16869/131072 : ℝ)) 4 (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16869/131072 : ℝ)) 5 (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16869/131072 : ℝ)) 6 (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16869/131072 : ℝ)) 7 (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16869/131072 : ℝ))) (88970435821/500000000000 : ℝ) (177940871649/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16869/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88970435821/500000000000 : ℝ) (177940871649/1000000000000 : ℝ) (588970435821/1000000000000 : ℝ) (23558817433/40000000000 : ℝ) (421830382549/1000000000000 : ℝ) (210915191279/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16869/131072 : ℝ))) 1 (588970435821/1000000000000 : ℝ) (23558817433/40000000000 : ℝ) (421830382549/1000000000000 : ℝ) (210915191279/500000000000 : ℝ) (101080081837/200000000000 : ℝ) (63175051149/125000000000 : ℝ) (124610800157/250000000000 : ℝ) (124610800159/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16869/131072 : ℝ))) 2 (101080081837/200000000000 : ℝ) (63175051149/125000000000 : ℝ) (124610800157/250000000000 : ℝ) (124610800159/250000000000 : ℝ) (250960902453/500000000000 : ℝ) (250960902457/500000000000 : ℝ) (250954875203/500000000000 : ℝ) (250954875207/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16869/131072 : ℝ))) 3 (250960902453/500000000000 : ℝ) (250960902457/500000000000 : ℝ) (250954875203/500000000000 : ℝ) (250954875207/500000000000 : ℝ) (62739472207/125000000000 : ℝ) (3921217013/7812500000 : ℝ) (501915777619/1000000000000 : ℝ) (125478944407/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16869/131072 : ℝ))) 4 (62739472207/125000000000 : ℝ) (3921217013/7812500000 : ℝ) (501915777619/1000000000000 : ℝ) (125478944407/250000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16869/131072 : ℝ))) 5 (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16869/131072 : ℝ))) 6 (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16869/131072 : ℝ))) 7 (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16869/131072 : ℝ)) hmem 8 (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16869/131072 : ℝ))) hcmem 8 (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16869/131072 : ℝ)) (992004544469/1000000000000 : ℝ) (124000568059/125000000000 : ℝ) (501915777637/1000000000000 : ℝ) (250957888823/500000000000 : ℝ) (24836310739/31250000000 : ℝ) (397380971833/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1305_exp_lower
  have heNumeric : (1027451720097/500000000000 : ℝ)/4 ≤ Real.exp (-42628192128999/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451720097/500000000000 : ℝ)/4 ≤ Real.exp ((33737/262144 : ℝ)-(397380971833/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33737/262144 : ℝ) (16869/131072 : ℝ) (397380971833/500000000000 : ℝ) (1027451720097/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1306; no trusted numerical premise.
theorem cover8_leaf1306_exp_radius : (997991019597879843/1000000000000000000 : ℝ) ≤ Real.exp ((-33739/2097152 : ℝ)/8) ∧ Real.exp ((-33739/2097152 : ℝ)/8) ≤ (249497754899469961/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33739/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1306_exp_lower : (230028389225401329/250000000000000000 : ℝ) ≤ Real.exp ((-21314095396171/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314095396171/32000000000000 : ℝ)/8) ≤ (920113556901605317/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314095396171/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1306_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903483111/1000000000000 : ℝ) ≤ 4*Real.exp (16869/131072 : ℝ)*Real.exp (-mu (radius 8 (33739/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903483111/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33739/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1306_exp_radius
  have hrNumeric : (492020355961/500000000000 : ℝ) ≤ Real.exp (-33739/2097152 : ℝ) ∧ Real.exp (-33739/2097152 : ℝ) ≤ (984040711923/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492020355961/500000000000 : ℝ) ≤ (radius 8 (33739/262144 : ℝ)) ∧ (radius 8 (33739/262144 : ℝ)) ≤ (984040711923/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33739/262144 : ℝ)) (492020355961/500000000000 : ℝ) (984040711923/1000000000000 : ℝ) (88971733261/500000000000 : ℝ) (177943466529/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33739/262144 : ℝ)) (492020355961/500000000000 : ℝ) (984040711923/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33739/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492020355961/500000000000 : ℝ) (984040711923/1000000000000 : ℝ) (992020355961/1000000000000 : ℝ) (496010177981/500000000000 : ℝ) (247997065497/250000000000 : ℝ) (991988261989/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33739/262144 : ℝ)) 1 (992020355961/1000000000000 : ℝ) (496010177981/500000000000 : ℝ) (247997065497/250000000000 : ℝ) (991988261989/1000000000000 : ℝ) (496002154487/500000000000 : ℝ) (62000269311/62500000000 : ℝ) (248001077211/250000000000 : ℝ) (496002154423/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33739/262144 : ℝ)) 2 (496002154487/500000000000 : ℝ) (62000269311/62500000000 : ℝ) (248001077211/250000000000 : ℝ) (496002154423/500000000000 : ℝ) (992004308909/1000000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33739/262144 : ℝ)) 3 (992004308909/1000000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33739/262144 : ℝ)) 4 (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33739/262144 : ℝ)) 5 (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33739/262144 : ℝ)) 6 (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33739/262144 : ℝ)) 7 (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33739/262144 : ℝ))) (88971733261/500000000000 : ℝ) (177943466529/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33739/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88971733261/500000000000 : ℝ) (177943466529/1000000000000 : ℝ) (588971733261/1000000000000 : ℝ) (117794346653/200000000000 : ℝ) (421833458277/1000000000000 : ℝ) (210916729143/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33739/262144 : ℝ))) 1 (588971733261/1000000000000 : ℝ) (117794346653/200000000000 : ℝ) (421833458277/1000000000000 : ℝ) (210916729143/500000000000 : ℝ) (505402595769/1000000000000 : ℝ) (7896915559/15625000000 : ℝ) (249222783403/500000000000 : ℝ) (249222783407/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33739/262144 : ℝ))) 2 (505402595769/1000000000000 : ℝ) (7896915559/15625000000 : ℝ) (249222783403/500000000000 : ℝ) (249222783407/500000000000 : ℝ) (501924081287/1000000000000 : ℝ) (100384816259/200000000000 : ℝ) (62739003433/125000000000 : ℝ) (31369501717/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33739/262144 : ℝ))) 3 (501924081287/1000000000000 : ℝ) (100384816259/200000000000 : ℝ) (62739003433/125000000000 : ℝ) (31369501717/62500000000 : ℝ) (803068887/1600000000 : ℝ) (31369878399/62500000000 : ℝ) (501918054339/1000000000000 : ℝ) (125479513587/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33739/262144 : ℝ))) 4 (803068887/1600000000 : ℝ) (31369878399/62500000000 : ℝ) (501918054339/1000000000000 : ℝ) (125479513587/250000000000 : ℝ) (501918054357/1000000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33739/262144 : ℝ))) 5 (501918054357/1000000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33739/262144 : ℝ))) 6 (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33739/262144 : ℝ))) 7 (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33739/262144 : ℝ)) hmem 8 (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33739/262144 : ℝ))) hcmem 8 (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33739/262144 : ℝ)) (248001077227/250000000000 : ℝ) (992004308911/1000000000000 : ℝ) (125479513589/250000000000 : ℝ) (250959027183/500000000000 : ℝ) (794765737459/1000000000000 : ℝ) (397382868739/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1306_exp_lower
  have heNumeric : (2054903483111/1000000000000 : ℝ)/4 ≤ Real.exp (-21314095396171/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903483111/1000000000000 : ℝ)/4 ≤ Real.exp ((16869/131072 : ℝ)-(397382868739/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16869/131072 : ℝ) (33739/262144 : ℝ) (397382868739/500000000000 : ℝ) (2054903483111/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1307; no trusted numerical premise.
theorem cover8_leaf1307_exp_radius : (249497740028245351/250000000000000000 : ℝ) ≤ Real.exp ((-8435/524288 : ℝ)/8) ∧ Real.exp ((-8435/524288 : ℝ)/8) ≤ (199598192022596281/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8435/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1307_exp_lower : (920113559312333389/1000000000000000000 : ℝ) ≤ Real.exp ((-8525637890177/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525637890177/12800000000000 : ℝ)/8) ≤ (92011355931233339/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525637890177/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1307_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451763091/500000000000 : ℝ) ≤ 4*Real.exp (33739/262144 : ℝ)*Real.exp (-mu (radius 8 (8435/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451763091/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8435/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1307_exp_radius
  have hrNumeric : (196808048539/200000000000 : ℝ) ≤ Real.exp (-8435/524288 : ℝ) ∧ Real.exp (-8435/524288 : ℝ) ≤ (123005030337/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196808048539/200000000000 : ℝ) ≤ (radius 8 (8435/65536 : ℝ)) ∧ (radius 8 (8435/65536 : ℝ)) ≤ (123005030337/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8435/65536 : ℝ)) (196808048539/200000000000 : ℝ) (123005030337/125000000000 : ℝ) (177946061363/1000000000000 : ℝ) (17794606137/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8435/65536 : ℝ)) (196808048539/200000000000 : ℝ) (123005030337/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8435/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196808048539/200000000000 : ℝ) (123005030337/125000000000 : ℝ) (992020121347/1000000000000 : ℝ) (248005030337/250000000000 : ℝ) (991988025479/1000000000000 : ℝ) (991988025481/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8435/65536 : ℝ)) 1 (992020121347/1000000000000 : ℝ) (248005030337/250000000000 : ℝ) (991988025479/1000000000000 : ℝ) (991988025481/1000000000000 : ℝ) (992004073413/1000000000000 : ℝ) (198400814683/200000000000 : ℝ) (992004073283/1000000000000 : ℝ) (198400814657/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8435/65536 : ℝ)) 2 (992004073413/1000000000000 : ℝ) (198400814683/200000000000 : ℝ) (992004073283/1000000000000 : ℝ) (198400814657/200000000000 : ℝ) (248001018337/250000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8435/65536 : ℝ)) 3 (248001018337/250000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8435/65536 : ℝ)) 4 (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8435/65536 : ℝ)) 5 (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8435/65536 : ℝ)) 6 (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8435/65536 : ℝ)) 7 (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8435/65536 : ℝ))) (177946061363/1000000000000 : ℝ) (17794606137/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8435/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177946061363/1000000000000 : ℝ) (17794606137/100000000000 : ℝ) (588973030681/1000000000000 : ℝ) (117794606137/200000000000 : ℝ) (84367306787/200000000000 : ℝ) (84367306789/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8435/65536 : ℝ))) 1 (588973030681/1000000000000 : ℝ) (117794606137/200000000000 : ℝ) (84367306787/200000000000 : ℝ) (84367306789/200000000000 : ℝ) (126351195577/250000000000 : ℝ) (101080956463/200000000000 : ℝ) (498447932931/1000000000000 : ℝ) (24922396647/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8435/65536 : ℝ))) 2 (126351195577/250000000000 : ℝ) (101080956463/200000000000 : ℝ) (498447932931/1000000000000 : ℝ) (24922396647/50000000000 : ℝ) (501926357619/1000000000000 : ℝ) (125481589407/250000000000 : ℝ) (501914304473/1000000000000 : ℝ) (250957152241/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8435/65536 : ℝ))) 3 (501926357619/1000000000000 : ℝ) (125481589407/250000000000 : ℝ) (501914304473/1000000000000 : ℝ) (250957152241/500000000000 : ℝ) (250960165523/500000000000 : ℝ) (100384066211/200000000000 : ℝ) (501920331009/1000000000000 : ℝ) (501920331019/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8435/65536 : ℝ))) 4 (250960165523/500000000000 : ℝ) (100384066211/200000000000 : ℝ) (501920331009/1000000000000 : ℝ) (501920331019/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8435/65536 : ℝ))) 5 (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8435/65536 : ℝ))) 6 (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8435/65536 : ℝ))) 7 (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8435/65536 : ℝ)) hmem 8 (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8435/65536 : ℝ))) hcmem 8 (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8435/65536 : ℝ)) (992004073347/1000000000000 : ℝ) (19840081467/20000000000 : ℝ) (501920331027/1000000000000 : ℝ) (501920331037/1000000000000 : ℝ) (158953906239/200000000000 : ℝ) (158953906243/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1307_exp_lower
  have heNumeric : (1027451763091/500000000000 : ℝ)/4 ≤ Real.exp (-8525637890177/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451763091/500000000000 : ℝ)/4 ≤ Real.exp ((33739/262144 : ℝ)-(158953906243/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33739/262144 : ℝ) (8435/65536 : ℝ) (158953906243/200000000000 : ℝ) (1027451763091/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1308; no trusted numerical premise.
theorem cover8_leaf1308_exp_radius : (99799090062808651/100000000000000000 : ℝ) ≤ Real.exp ((-33741/2097152 : ℝ)/8) ∧ Real.exp ((-33741/2097152 : ℝ)/8) ≤ (997990900628086511/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33741/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1308_exp_lower : (230028390432921883/250000000000000000 : ℝ) ≤ Real.exp ((-10657047026157/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657047026157/16000000000000 : ℝ)/8) ≤ (920113561731687533/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657047026157/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1308_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2006741767/976562500 : ℝ) ≤ 4*Real.exp (8435/65536 : ℝ)*Real.exp (-mu (radius 8 (33741/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2006741767/976562500 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33741/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1308_exp_radius
  have hrNumeric : (246009943367/250000000000 : ℝ) ≤ Real.exp (-33741/2097152 : ℝ) ∧ Real.exp (-33741/2097152 : ℝ) ≤ (984039773469/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246009943367/250000000000 : ℝ) ≤ (radius 8 (33741/262144 : ℝ)) ∧ (radius 8 (33741/262144 : ℝ)) ≤ (984039773469/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33741/262144 : ℝ)) (246009943367/250000000000 : ℝ) (984039773469/1000000000000 : ℝ) (35589731233/200000000000 : ℝ) (177948656171/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33741/262144 : ℝ)) (246009943367/250000000000 : ℝ) (984039773469/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33741/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246009943367/250000000000 : ℝ) (984039773469/1000000000000 : ℝ) (496009943367/500000000000 : ℝ) (198403977347/200000000000 : ℝ) (991987788971/1000000000000 : ℝ) (247996947243/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33741/262144 : ℝ)) 1 (496009943367/500000000000 : ℝ) (198403977347/200000000000 : ℝ) (991987788971/1000000000000 : ℝ) (247996947243/250000000000 : ℝ) (248000959463/250000000000 : ℝ) (496001918927/500000000000 : ℝ) (496001918861/500000000000 : ℝ) (248000959431/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33741/262144 : ℝ)) 2 (248000959463/250000000000 : ℝ) (496001918927/500000000000 : ℝ) (496001918861/500000000000 : ℝ) (248000959431/250000000000 : ℝ) (992003837787/1000000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33741/262144 : ℝ)) 3 (992003837787/1000000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33741/262144 : ℝ)) 4 (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33741/262144 : ℝ)) 5 (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33741/262144 : ℝ)) 6 (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33741/262144 : ℝ)) 7 (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33741/262144 : ℝ))) (35589731233/200000000000 : ℝ) (177948656171/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33741/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35589731233/200000000000 : ℝ) (177948656171/1000000000000 : ℝ) (294487164041/500000000000 : ℝ) (294487164043/500000000000 : ℝ) (16873584381/40000000000 : ℝ) (210919804767/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33741/262144 : ℝ))) 1 (294487164041/500000000000 : ℝ) (294487164043/500000000000 : ℝ) (16873584381/40000000000 : ℝ) (210919804767/500000000000 : ℝ) (505406968803/1000000000000 : ℝ) (50540696881/100000000000 : ℝ) (99690059801/200000000000 : ℝ) (498450299013/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33741/262144 : ℝ))) 2 (505406968803/1000000000000 : ℝ) (50540696881/100000000000 : ℝ) (99690059801/200000000000 : ℝ) (498450299013/1000000000000 : ℝ) (31370539619/62500000000 : ℝ) (62741079239/125000000000 : ℝ) (250958290717/500000000000 : ℝ) (501916581443/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33741/262144 : ℝ))) 3 (31370539619/62500000000 : ℝ) (62741079239/125000000000 : ℝ) (250958290717/500000000000 : ℝ) (501916581443/1000000000000 : ℝ) (501922607669/1000000000000 : ℝ) (250961303839/500000000000 : ℝ) (31370162977/62500000000 : ℝ) (250961303821/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33741/262144 : ℝ))) 4 (501922607669/1000000000000 : ℝ) (250961303839/500000000000 : ℝ) (31370162977/62500000000 : ℝ) (250961303821/500000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33741/262144 : ℝ))) 5 (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33741/262144 : ℝ))) 6 (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33741/262144 : ℝ))) 7 (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33741/262144 : ℝ)) hmem 8 (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33741/262144 : ℝ))) hcmem 8 (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33741/262144 : ℝ)) (496001918893/500000000000 : ℝ) (992003837789/1000000000000 : ℝ) (10038452153/20000000000 : ℝ) (25096130383/50000000000 : ℝ) (397386662429/500000000000 : ℝ) (794773324877/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1308_exp_lower
  have heNumeric : (2006741767/976562500 : ℝ)/4 ≤ Real.exp (-10657047026157/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2006741767/976562500 : ℝ)/4 ≤ Real.exp ((8435/65536 : ℝ)-(794773324877/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8435/65536 : ℝ) (33741/262144 : ℝ) (794773324877/1000000000000 : ℝ) (2006741767/976562500 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1309; no trusted numerical premise.
theorem cover8_leaf1309_exp_radius : (498995420571597581/500000000000000000 : ℝ) ≤ Real.exp ((-16871/1048576 : ℝ)/8) ∧ Real.exp ((-16871/1048576 : ℝ)/8) ≤ (997990841143195163/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16871/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1309_exp_lower : (920113564160472847/1000000000000000000 : ℝ) ≤ Real.exp ((-42628186753123/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628186753123/64000000000000 : ℝ)/8) ≤ (57507097760029553/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628186753123/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1309_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451806401/500000000000 : ℝ) ≤ 4*Real.exp (33741/262144 : ℝ)*Real.exp (-mu (radius 8 (16871/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451806401/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16871/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1309_exp_radius
  have hrNumeric : (492019652121/500000000000 : ℝ) ≤ Real.exp (-16871/1048576 : ℝ) ∧ Real.exp (-16871/1048576 : ℝ) ≤ (984039304243/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492019652121/500000000000 : ℝ) ≤ (radius 8 (16871/131072 : ℝ)) ∧ (radius 8 (16871/131072 : ℝ)) ≤ (984039304243/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16871/131072 : ℝ)) (492019652121/500000000000 : ℝ) (984039304243/1000000000000 : ℝ) (88975625461/500000000000 : ℝ) (177951250929/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16871/131072 : ℝ)) (492019652121/500000000000 : ℝ) (984039304243/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16871/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492019652121/500000000000 : ℝ) (984039304243/1000000000000 : ℝ) (992019652121/1000000000000 : ℝ) (496009826061/500000000000 : ℝ) (991987552463/1000000000000 : ℝ) (61999222029/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16871/131072 : ℝ)) 1 (992019652121/1000000000000 : ℝ) (496009826061/500000000000 : ℝ) (991987552463/1000000000000 : ℝ) (61999222029/62500000000 : ℝ) (248000900573/250000000000 : ℝ) (992003602293/1000000000000 : ℝ) (496001801081/500000000000 : ℝ) (248000900541/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16871/131072 : ℝ)) 2 (248000900573/250000000000 : ℝ) (992003602293/1000000000000 : ℝ) (496001801081/500000000000 : ℝ) (248000900541/250000000000 : ℝ) (992003602227/1000000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16871/131072 : ℝ)) 3 (992003602227/1000000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16871/131072 : ℝ)) 4 (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16871/131072 : ℝ)) 5 (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16871/131072 : ℝ)) 6 (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16871/131072 : ℝ)) 7 (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16871/131072 : ℝ))) (88975625461/500000000000 : ℝ) (177951250929/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16871/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88975625461/500000000000 : ℝ) (177951250929/1000000000000 : ℝ) (588975625461/1000000000000 : ℝ) (117795125093/200000000000 : ℝ) (5273033563/12500000000 : ℝ) (421842685049/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16871/131072 : ℝ))) 1 (588975625461/1000000000000 : ℝ) (117795125093/200000000000 : ℝ) (5273033563/12500000000 : ℝ) (421842685049/1000000000000 : ℝ) (2021636621/4000000000 : ℝ) (505409155257/1000000000000 : ℝ) (249226332511/500000000000 : ℝ) (49845266503/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16871/131072 : ℝ))) 2 (2021636621/4000000000 : ℝ) (505409155257/1000000000000 : ℝ) (249226332511/500000000000 : ℝ) (49845266503/100000000000 : ℝ) (62741363767/125000000000 : ℝ) (7842670471/15625000000 : ℝ) (501918858343/1000000000000 : ℝ) (31369928647/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16871/131072 : ℝ))) 3 (62741363767/125000000000 : ℝ) (7842670471/15625000000 : ℝ) (501918858343/1000000000000 : ℝ) (31369928647/62500000000 : ℝ) (501924884239/1000000000000 : ℝ) (62740610531/125000000000 : ℝ) (501924884203/1000000000000 : ℝ) (125481221053/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16871/131072 : ℝ))) 4 (501924884239/1000000000000 : ℝ) (62740610531/125000000000 : ℝ) (501924884203/1000000000000 : ℝ) (125481221053/250000000000 : ℝ) (501924884221/1000000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16871/131072 : ℝ))) 5 (501924884221/1000000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16871/131072 : ℝ))) 6 (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16871/131072 : ℝ))) 7 (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16871/131072 : ℝ)) hmem 8 (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16871/131072 : ℝ))) hcmem 8 (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16871/131072 : ℝ)) (496001801113/500000000000 : ℝ) (992003602229/1000000000000 : ℝ) (25096244211/50000000000 : ℝ) (50192488423/100000000000 : ℝ) (397388559219/500000000000 : ℝ) (794777118457/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1309_exp_lower
  have heNumeric : (1027451806401/500000000000 : ℝ)/4 ≤ Real.exp (-42628186753123/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451806401/500000000000 : ℝ)/4 ≤ Real.exp ((33741/262144 : ℝ)-(794777118457/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33741/262144 : ℝ) (16871/131072 : ℝ) (794777118457/1000000000000 : ℝ) (1027451806401/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1310; no trusted numerical premise.
theorem cover8_leaf1310_exp_radius : (997990781658307359/1000000000000000000 : ℝ) ≤ Real.exp ((-33743/2097152 : ℝ)/8) ∧ Real.exp ((-33743/2097152 : ℝ)/8) ≤ (6237442385364421/6250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33743/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1310_exp_lower : (460056783298482059/500000000000000000 : ℝ) ≤ Real.exp ((-4262818539733/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262818539733/6400000000000 : ℝ)/8) ≤ (920113566596964119/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262818539733/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1310_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903656333/1000000000000 : ℝ) ≤ 4*Real.exp (16871/131072 : ℝ)*Real.exp (-mu (radius 8 (33743/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903656333/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33743/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1310_exp_radius
  have hrNumeric : (196807767003/200000000000 : ℝ) ≤ Real.exp (-33743/2097152 : ℝ) ∧ Real.exp (-33743/2097152 : ℝ) ≤ (123004854377/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196807767003/200000000000 : ℝ) ≤ (radius 8 (33743/262144 : ℝ)) ∧ (radius 8 (33743/262144 : ℝ)) ≤ (123004854377/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33743/262144 : ℝ)) (196807767003/200000000000 : ℝ) (123004854377/125000000000 : ℝ) (88976922823/500000000000 : ℝ) (44488461413/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33743/262144 : ℝ)) (196807767003/200000000000 : ℝ) (123004854377/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33743/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196807767003/200000000000 : ℝ) (123004854377/125000000000 : ℝ) (992019417507/1000000000000 : ℝ) (248004854377/250000000000 : ℝ) (495993657977/500000000000 : ℝ) (247996828989/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33743/262144 : ℝ)) 1 (992019417507/1000000000000 : ℝ) (248004854377/250000000000 : ℝ) (495993657977/500000000000 : ℝ) (247996828989/250000000000 : ℝ) (99200336673/100000000000 : ℝ) (248000841683/250000000000 : ℝ) (4960016833/5000000000 : ℝ) (992003366603/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33743/262144 : ℝ)) 2 (99200336673/100000000000 : ℝ) (248000841683/250000000000 : ℝ) (4960016833/5000000000 : ℝ) (992003366603/1000000000000 : ℝ) (198400673333/200000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33743/262144 : ℝ)) 3 (198400673333/200000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33743/262144 : ℝ)) 4 (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33743/262144 : ℝ)) 5 (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33743/262144 : ℝ)) 6 (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33743/262144 : ℝ)) 7 (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33743/262144 : ℝ))) (88976922823/500000000000 : ℝ) (44488461413/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33743/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88976922823/500000000000 : ℝ) (44488461413/250000000000 : ℝ) (588976922823/1000000000000 : ℝ) (294488461413/500000000000 : ℝ) (421845760493/1000000000000 : ℝ) (421845760501/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33743/262144 : ℝ))) 1 (588976922823/1000000000000 : ℝ) (294488461413/500000000000 : ℝ) (421845760493/1000000000000 : ℝ) (421845760501/1000000000000 : ℝ) (252705670829/500000000000 : ℝ) (15794104427/31250000000 : ℝ) (498455030991/1000000000000 : ℝ) (249227515499/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33743/262144 : ℝ))) 2 (252705670829/500000000000 : ℝ) (15794104427/31250000000 : ℝ) (498455030991/1000000000000 : ℝ) (249227515499/500000000000 : ℝ) (125483296581/250000000000 : ℝ) (501933186331/1000000000000 : ℝ) (62740141901/125000000000 : ℝ) (31370070951/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33743/262144 : ℝ))) 3 (125483296581/250000000000 : ℝ) (501933186331/1000000000000 : ℝ) (62740141901/125000000000 : ℝ) (31370070951/62500000000 : ℝ) (250963580383/500000000000 : ℝ) (250963580387/500000000000 : ℝ) (501927160729/1000000000000 : ℝ) (250963580369/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33743/262144 : ℝ))) 4 (250963580383/500000000000 : ℝ) (250963580387/500000000000 : ℝ) (501927160729/1000000000000 : ℝ) (250963580369/500000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33743/262144 : ℝ))) 5 (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33743/262144 : ℝ))) 6 (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33743/262144 : ℝ))) 7 (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33743/262144 : ℝ)) hmem 8 (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33743/262144 : ℝ))) hcmem 8 (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33743/262144 : ℝ)) (124000420833/125000000000 : ℝ) (248000841667/250000000000 : ℝ) (501927160747/1000000000000 : ℝ) (125481790189/250000000000 : ℝ) (49673806997/62500000000 : ℝ) (79478091197/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1310_exp_lower
  have heNumeric : (2054903656333/1000000000000 : ℝ)/4 ≤ Real.exp (-4262818539733/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903656333/1000000000000 : ℝ)/4 ≤ Real.exp ((16871/131072 : ℝ)-(79478091197/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16871/131072 : ℝ) (33743/262144 : ℝ) (79478091197/100000000000 : ℝ) (2054903656333/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1311; no trusted numerical premise.
theorem cover8_leaf1311_exp_radius : (498995361086711551/500000000000000000 : ℝ) ≤ Real.exp ((-2109/131072 : ℝ)/8) ∧ Real.exp ((-2109/131072 : ℝ)/8) ≤ (997990722173423103/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2109/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1311_exp_lower : (920113569042886561/1000000000000000000 : ℝ) ≤ Real.exp ((-42628184036289/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628184036289/64000000000000 : ℝ)/8) ≤ (460056784521443281/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628184036289/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1311_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451850017/500000000000 : ℝ) ≤ 4*Real.exp (33743/262144 : ℝ)*Real.exp (-mu (radius 8 (2109/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451850017/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2109/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1311_exp_radius
  have hrNumeric : (984038365789/1000000000000 : ℝ) ≤ Real.exp (-2109/131072 : ℝ) ∧ Real.exp (-2109/131072 : ℝ) ≤ (98403836579/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984038365789/1000000000000 : ℝ) ≤ (radius 8 (2109/16384 : ℝ)) ∧ (radius 8 (2109/16384 : ℝ)) ≤ (98403836579/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2109/16384 : ℝ)) (984038365789/1000000000000 : ℝ) (98403836579/100000000000 : ℝ) (7118257613/40000000000 : ℝ) (44489110083/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2109/16384 : ℝ)) (984038365789/1000000000000 : ℝ) (98403836579/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2109/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984038365789/1000000000000 : ℝ) (98403836579/100000000000 : ℝ) (496009591447/500000000000 : ℝ) (198403836579/200000000000 : ℝ) (495993539723/500000000000 : ℝ) (123998384931/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2109/16384 : ℝ)) 1 (496009591447/500000000000 : ℝ) (198403836579/200000000000 : ℝ) (495993539723/500000000000 : ℝ) (123998384931/125000000000 : ℝ) (99200313117/100000000000 : ℝ) (248000782793/250000000000 : ℝ) (6200019569/6250000000 : ℝ) (496001565521/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2109/16384 : ℝ)) 2 (99200313117/100000000000 : ℝ) (248000782793/250000000000 : ℝ) (6200019569/6250000000 : ℝ) (496001565521/500000000000 : ℝ) (198400626221/200000000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2109/16384 : ℝ)) 3 (198400626221/200000000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2109/16384 : ℝ)) 4 (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2109/16384 : ℝ)) 5 (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2109/16384 : ℝ)) 6 (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2109/16384 : ℝ)) 7 (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2109/16384 : ℝ))) (7118257613/40000000000 : ℝ) (44489110083/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2109/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7118257613/40000000000 : ℝ) (44489110083/250000000000 : ℝ) (294489110081/500000000000 : ℝ) (294489110083/500000000000 : ℝ) (42184883587/100000000000 : ℝ) (421848835879/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2109/16384 : ℝ))) 1 (294489110081/500000000000 : ℝ) (294489110083/500000000000 : ℝ) (42184883587/100000000000 : ℝ) (421848835879/1000000000000 : ℝ) (31588345501/62500000000 : ℝ) (505413528023/1000000000000 : ℝ) (498457396903/1000000000000 : ℝ) (498457396911/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2109/16384 : ℝ))) 2 (31588345501/62500000000 : ℝ) (505413528023/1000000000000 : ℝ) (498457396903/1000000000000 : ℝ) (498457396911/1000000000000 : ℝ) (501935462459/1000000000000 : ℝ) (501935462467/1000000000000 : ℝ) (25096170601/50000000000 : ℝ) (501923412029/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2109/16384 : ℝ))) 3 (501935462459/1000000000000 : ℝ) (501935462467/1000000000000 : ℝ) (25096170601/50000000000 : ℝ) (501923412029/1000000000000 : ℝ) (501929437239/1000000000000 : ℝ) (7842647457/15625000000 : ℝ) (501929437203/1000000000000 : ℝ) (125482359303/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2109/16384 : ℝ))) 4 (501929437239/1000000000000 : ℝ) (7842647457/15625000000 : ℝ) (501929437203/1000000000000 : ℝ) (125482359303/250000000000 : ℝ) (501929437221/1000000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2109/16384 : ℝ))) 5 (501929437221/1000000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2109/16384 : ℝ))) 6 (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2109/16384 : ℝ))) 7 (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2109/16384 : ℝ)) hmem 8 (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2109/16384 : ℝ))) hcmem 8 (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2109/16384 : ℝ)) (31000097847/31250000000 : ℝ) (992003131107/1000000000000 : ℝ) (25096471861/50000000000 : ℝ) (50192943723/100000000000 : ℝ) (397392352691/500000000000 : ℝ) (794784705401/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1311_exp_lower
  have heNumeric : (1027451850017/500000000000 : ℝ)/4 ≤ Real.exp (-42628184036289/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451850017/500000000000 : ℝ)/4 ≤ Real.exp ((33743/262144 : ℝ)-(794784705401/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33743/262144 : ℝ) (2109/16384 : ℝ) (794784705401/1000000000000 : ℝ) (1027451850017/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1312; no trusted numerical premise.
theorem cover8_leaf1312_exp_radius : (99799066268854239/100000000000000000 : ℝ) ≤ Real.exp ((-33745/2097152 : ℝ)/8) ∧ Real.exp ((-33745/2097152 : ℝ)/8) ≤ (997990662688542391/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33745/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1312_exp_lower : (460056785748717537/500000000000000000 : ℝ) ≤ Real.exp ((-2664261416903/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664261416903/4000000000000 : ℝ)/8) ≤ (36804542859897403/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664261416903/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1312_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431483993/62500000000 : ℝ) ≤ 4*Real.exp (2109/16384 : ℝ)*Real.exp (-mu (radius 8 (33745/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (128431483993/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33745/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1312_exp_radius
  have hrNumeric : (984037896563/1000000000000 : ℝ) ≤ Real.exp (-33745/2097152 : ℝ) ∧ Real.exp (-33745/2097152 : ℝ) ≤ (246009474141/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984037896563/1000000000000 : ℝ) ≤ (radius 8 (33745/262144 : ℝ)) ∧ (radius 8 (33745/262144 : ℝ)) ≤ (246009474141/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33745/262144 : ℝ)) (984037896563/1000000000000 : ℝ) (246009474141/250000000000 : ℝ) (35591806993/200000000000 : ℝ) (44489758743/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33745/262144 : ℝ)) (984037896563/1000000000000 : ℝ) (246009474141/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33745/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984037896563/1000000000000 : ℝ) (246009474141/250000000000 : ℝ) (992018948281/1000000000000 : ℝ) (496009474141/500000000000 : ℝ) (495993421469/500000000000 : ℝ) (991986842939/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33745/262144 : ℝ)) 1 (992018948281/1000000000000 : ℝ) (496009474141/500000000000 : ℝ) (495993421469/500000000000 : ℝ) (991986842939/1000000000000 : ℝ) (992002895609/1000000000000 : ℝ) (992002895611/1000000000000 : ℝ) (992002895479/1000000000000 : ℝ) (992002895481/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33745/262144 : ℝ)) 2 (992002895609/1000000000000 : ℝ) (992002895611/1000000000000 : ℝ) (992002895479/1000000000000 : ℝ) (992002895481/1000000000000 : ℝ) (124000361943/125000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33745/262144 : ℝ)) 3 (124000361943/125000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33745/262144 : ℝ)) 4 (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33745/262144 : ℝ)) 5 (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33745/262144 : ℝ)) 6 (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33745/262144 : ℝ)) 7 (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33745/262144 : ℝ))) (35591806993/200000000000 : ℝ) (44489758743/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33745/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35591806993/200000000000 : ℝ) (44489758743/250000000000 : ℝ) (294489758741/500000000000 : ℝ) (294489758743/500000000000 : ℝ) (210925955589/500000000000 : ℝ) (421851911187/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33745/262144 : ℝ))) 1 (294489758741/500000000000 : ℝ) (294489758743/500000000000 : ℝ) (210925955589/500000000000 : ℝ) (421851911187/1000000000000 : ℝ) (50541571433/100000000000 : ℝ) (505415714337/1000000000000 : ℝ) (498459762763/1000000000000 : ℝ) (498459762771/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33745/262144 : ℝ))) 2 (50541571433/100000000000 : ℝ) (505415714337/1000000000000 : ℝ) (498459762763/1000000000000 : ℝ) (498459762771/1000000000000 : ℝ) (250968869273/500000000000 : ℝ) (250968869277/500000000000 : ℝ) (31370355549/62500000000 : ℝ) (62740711099/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33745/262144 : ℝ))) 3 (250968869273/500000000000 : ℝ) (250968869277/500000000000 : ℝ) (31370355549/62500000000 : ℝ) (62740711099/125000000000 : ℝ) (100386342733/200000000000 : ℝ) (501931713673/1000000000000 : ℝ) (125482928407/250000000000 : ℝ) (501931713637/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33745/262144 : ℝ))) 4 (100386342733/200000000000 : ℝ) (501931713673/1000000000000 : ℝ) (125482928407/250000000000 : ℝ) (501931713637/1000000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33745/262144 : ℝ))) 5 (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33745/262144 : ℝ))) 6 (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33745/262144 : ℝ))) 7 (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33745/262144 : ℝ)) hmem 8 (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33745/262144 : ℝ))) hcmem 8 (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33745/262144 : ℝ)) (992002895543/1000000000000 : ℝ) (496001447773/500000000000 : ℝ) (250965856823/500000000000 : ℝ) (100386342731/200000000000 : ℝ) (39739424937/50000000000 : ℝ) (794788498757/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1312_exp_lower
  have heNumeric : (128431483993/62500000000 : ℝ)/4 ≤ Real.exp (-2664261416903/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431483993/62500000000 : ℝ)/4 ≤ Real.exp ((2109/16384 : ℝ)-(794788498757/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2109/16384 : ℝ) (33745/262144 : ℝ) (794788498757/1000000000000 : ℝ) (128431483993/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1313; no trusted numerical premise.
theorem cover8_leaf1313_exp_radius : (124748825400458153/125000000000000000 : ℝ) ≤ Real.exp ((-16873/1048576 : ℝ)/8) ∧ Real.exp ((-16873/1048576 : ℝ)/8) ≤ (39919624128146609/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16873/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1313_exp_lower : (460056786980074801/500000000000000000 : ℝ) ≤ Real.exp ((-42628181300063/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628181300063/64000000000000 : ℝ)/8) ≤ (920113573960149603/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628181300063/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1313_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431486743/62500000000 : ℝ) ≤ 4*Real.exp (33745/262144 : ℝ)*Real.exp (-mu (radius 8 (16873/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (128431486743/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16873/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1313_exp_radius
  have hrNumeric : (984037427337/1000000000000 : ℝ) ≤ Real.exp (-16873/1048576 : ℝ) ∧ Real.exp (-16873/1048576 : ℝ) ≤ (492018713669/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984037427337/1000000000000 : ℝ) ≤ (radius 8 (16873/131072 : ℝ)) ∧ (radius 8 (16873/131072 : ℝ)) ≤ (492018713669/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16873/131072 : ℝ)) (984037427337/1000000000000 : ℝ) (492018713669/500000000000 : ℝ) (88980814783/500000000000 : ℝ) (177961629573/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16873/131072 : ℝ)) (984037427337/1000000000000 : ℝ) (492018713669/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16873/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984037427337/1000000000000 : ℝ) (492018713669/500000000000 : ℝ) (248004678417/250000000000 : ℝ) (992018713669/1000000000000 : ℝ) (99198660643/100000000000 : ℝ) (991986606431/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16873/131072 : ℝ)) 1 (248004678417/250000000000 : ℝ) (992018713669/1000000000000 : ℝ) (99198660643/100000000000 : ℝ) (991986606431/1000000000000 : ℝ) (992002660049/1000000000000 : ℝ) (19840053201/20000000000 : ℝ) (992002659919/1000000000000 : ℝ) (992002659921/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16873/131072 : ℝ)) 2 (992002660049/1000000000000 : ℝ) (19840053201/20000000000 : ℝ) (992002659919/1000000000000 : ℝ) (992002659921/1000000000000 : ℝ) (62000166249/62500000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16873/131072 : ℝ)) 3 (62000166249/62500000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16873/131072 : ℝ)) 4 (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16873/131072 : ℝ)) 5 (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16873/131072 : ℝ)) 6 (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16873/131072 : ℝ)) 7 (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16873/131072 : ℝ))) (88980814783/500000000000 : ℝ) (177961629573/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16873/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88980814783/500000000000 : ℝ) (177961629573/1000000000000 : ℝ) (588980814783/1000000000000 : ℝ) (588980814787/1000000000000 : ℝ) (210927493209/500000000000 : ℝ) (421854986427/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16873/131072 : ℝ))) 1 (588980814783/1000000000000 : ℝ) (588980814787/1000000000000 : ℝ) (210927493209/500000000000 : ℝ) (421854986427/1000000000000 : ℝ) (2527089503/5000000000 : ℝ) (505417900607/1000000000000 : ℝ) (124615532143/250000000000 : ℝ) (24923106429/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16873/131072 : ℝ))) 2 (2527089503/5000000000 : ℝ) (505417900607/1000000000000 : ℝ) (124615532143/250000000000 : ℝ) (24923106429/50000000000 : ℝ) (250970007293/500000000000 : ℝ) (250970007297/500000000000 : ℝ) (1003855931/2000000000 : ℝ) (501927965509/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16873/131072 : ℝ))) 3 (250970007293/500000000000 : ℝ) (250970007297/500000000000 : ℝ) (1003855931/2000000000 : ℝ) (501927965509/1000000000000 : ℝ) (501933990043/1000000000000 : ℝ) (125483497513/250000000000 : ℝ) (250966995003/500000000000 : ℝ) (3921359297/7812500000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16873/131072 : ℝ))) 4 (501933990043/1000000000000 : ℝ) (125483497513/250000000000 : ℝ) (250966995003/500000000000 : ℝ) (3921359297/7812500000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16873/131072 : ℝ))) 5 (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16873/131072 : ℝ))) 6 (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16873/131072 : ℝ))) 7 (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16873/131072 : ℝ)) hmem 8 (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16873/131072 : ℝ))) hcmem 8 (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16873/131072 : ℝ)) (992002659983/1000000000000 : ℝ) (496001329993/500000000000 : ℝ) (62741748753/125000000000 : ℝ) (250966995017/500000000000 : ℝ) (794792292023/1000000000000 : ℝ) (397396146021/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1313_exp_lower
  have heNumeric : (128431486743/62500000000 : ℝ)/4 ≤ Real.exp (-42628181300063/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431486743/62500000000 : ℝ)/4 ≤ Real.exp ((33745/262144 : ℝ)-(397396146021/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33745/262144 : ℝ) (16873/131072 : ℝ) (397396146021/500000000000 : ℝ) (128431486743/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1314; no trusted numerical premise.
theorem cover8_leaf1314_exp_radius : (249497635929697901/250000000000000000 : ℝ) ≤ Real.exp ((-33747/2097152 : ℝ)/8) ∧ Real.exp ((-33747/2097152 : ℝ)/8) ≤ (199598108743758321/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33747/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1314_exp_lower : (460056788216492693/500000000000000000 : ℝ) ≤ Real.exp ((-21314089962023/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314089962023/32000000000000 : ℝ)/8) ≤ (920113576432985387/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314089962023/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1314_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903832069/1000000000000 : ℝ) ≤ 4*Real.exp (16873/131072 : ℝ)*Real.exp (-mu (radius 8 (33747/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903832069/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33747/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1314_exp_radius
  have hrNumeric : (30751154941/31250000000 : ℝ) ≤ Real.exp (-33747/2097152 : ℝ) ∧ Real.exp (-33747/2097152 : ℝ) ≤ (984036958113/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30751154941/31250000000 : ℝ) ≤ (radius 8 (33747/262144 : ℝ)) ∧ (radius 8 (33747/262144 : ℝ)) ≤ (984036958113/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33747/262144 : ℝ)) (30751154941/31250000000 : ℝ) (984036958113/1000000000000 : ℝ) (177964224123/1000000000000 : ℝ) (177964224129/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33747/262144 : ℝ)) (30751154941/31250000000 : ℝ) (984036958113/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33747/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30751154941/31250000000 : ℝ) (984036958113/1000000000000 : ℝ) (62001154941/62500000000 : ℝ) (992018479057/1000000000000 : ℝ) (495993184961/500000000000 : ℝ) (991986369923/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33747/262144 : ℝ)) 1 (62001154941/62500000000 : ℝ) (992018479057/1000000000000 : ℝ) (495993184961/500000000000 : ℝ) (991986369923/1000000000000 : ℝ) (992002424489/1000000000000 : ℝ) (99200242449/100000000000 : ℝ) (992002424359/1000000000000 : ℝ) (992002424361/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33747/262144 : ℝ)) 2 (992002424489/1000000000000 : ℝ) (99200242449/100000000000 : ℝ) (992002424359/1000000000000 : ℝ) (992002424361/1000000000000 : ℝ) (124000303053/125000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33747/262144 : ℝ)) 3 (124000303053/125000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33747/262144 : ℝ)) 4 (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33747/262144 : ℝ)) 5 (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33747/262144 : ℝ)) 6 (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33747/262144 : ℝ)) 7 (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33747/262144 : ℝ))) (177964224123/1000000000000 : ℝ) (177964224129/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33747/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177964224123/1000000000000 : ℝ) (177964224129/1000000000000 : ℝ) (588982112061/1000000000000 : ℝ) (117796422413/200000000000 : ℝ) (421858061583/1000000000000 : ℝ) (421858061591/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33747/262144 : ℝ))) 1 (588982112061/1000000000000 : ℝ) (117796422413/200000000000 : ℝ) (421858061583/1000000000000 : ℝ) (421858061591/1000000000000 : ℝ) (252710043411/500000000000 : ℝ) (126355021707/250000000000 : ℝ) (498464494323/1000000000000 : ℝ) (49846449433/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33747/262144 : ℝ))) 2 (252710043411/500000000000 : ℝ) (126355021707/250000000000 : ℝ) (498464494323/1000000000000 : ℝ) (49846449433/100000000000 : ℝ) (125485572643/250000000000 : ℝ) (501942290579/1000000000000 : ℝ) (501930242163/1000000000000 : ℝ) (501930242171/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33747/262144 : ℝ))) 3 (125485572643/250000000000 : ℝ) (501942290579/1000000000000 : ℝ) (501930242163/1000000000000 : ℝ) (501930242171/1000000000000 : ℝ) (501936266367/1000000000000 : ℝ) (4015490131/8000000000 : ℝ) (501936266331/1000000000000 : ℝ) (501936266339/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33747/262144 : ℝ))) 4 (501936266367/1000000000000 : ℝ) (4015490131/8000000000 : ℝ) (501936266331/1000000000000 : ℝ) (501936266339/1000000000000 : ℝ) (501936266349/1000000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33747/262144 : ℝ))) 5 (501936266349/1000000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33747/262144 : ℝ))) 6 (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33747/262144 : ℝ))) 7 (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33747/262144 : ℝ)) hmem 8 (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33747/262144 : ℝ))) hcmem 8 (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33747/262144 : ℝ)) (992002424423/1000000000000 : ℝ) (496001212213/500000000000 : ℝ) (125484066587/250000000000 : ℝ) (501936266357/1000000000000 : ℝ) (397398042611/500000000000 : ℝ) (794796085239/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1314_exp_lower
  have heNumeric : (2054903832069/1000000000000 : ℝ)/4 ≤ Real.exp (-21314089962023/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903832069/1000000000000 : ℝ)/4 ≤ Real.exp ((16873/131072 : ℝ)-(794796085239/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16873/131072 : ℝ) (33747/262144 : ℝ) (794796085239/1000000000000 : ℝ) (2054903832069/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1315; no trusted numerical premise.
theorem cover8_leaf1315_exp_radius : (997990484233921529/1000000000000000000 : ℝ) ≤ Real.exp ((-8437/524288 : ℝ)/8) ∧ Real.exp ((-8437/524288 : ℝ)/8) ≤ (99799048423392153/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8437/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1315_exp_lower : (184022715782797437/200000000000000000 : ℝ) ≤ Real.exp ((-8525635708697/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525635708697/12800000000000 : ℝ)/8) ≤ (460056789456993593/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525635708697/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1315_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725969099/250000000000 : ℝ) ≤ 4*Real.exp (33747/262144 : ℝ)*Real.exp (-mu (radius 8 (8437/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513725969099/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8437/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1315_exp_radius
  have hrNumeric : (984036488887/1000000000000 : ℝ) ≤ Real.exp (-8437/524288 : ℝ) ∧ Real.exp (-8437/524288 : ℝ) ≤ (123004561111/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984036488887/1000000000000 : ℝ) ≤ (radius 8 (8437/65536 : ℝ)) ∧ (radius 8 (8437/65536 : ℝ)) ≤ (123004561111/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8437/65536 : ℝ)) (984036488887/1000000000000 : ℝ) (123004561111/125000000000 : ℝ) (2224585233/12500000000 : ℝ) (88983409323/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8437/65536 : ℝ)) (984036488887/1000000000000 : ℝ) (123004561111/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8437/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984036488887/1000000000000 : ℝ) (123004561111/125000000000 : ℝ) (992018244443/1000000000000 : ℝ) (248004561111/250000000000 : ℝ) (495993066707/500000000000 : ℝ) (123998266677/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8437/65536 : ℝ)) 1 (992018244443/1000000000000 : ℝ) (248004561111/250000000000 : ℝ) (495993066707/500000000000 : ℝ) (123998266677/125000000000 : ℝ) (7750017101/7812500000 : ℝ) (99200218893/100000000000 : ℝ) (496001094399/500000000000 : ℝ) (992002188801/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8437/65536 : ℝ)) 2 (7750017101/7812500000 : ℝ) (99200218893/100000000000 : ℝ) (496001094399/500000000000 : ℝ) (992002188801/1000000000000 : ℝ) (992002188863/1000000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8437/65536 : ℝ)) 3 (992002188863/1000000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8437/65536 : ℝ)) 4 (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8437/65536 : ℝ)) 5 (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8437/65536 : ℝ)) 6 (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8437/65536 : ℝ)) 7 (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8437/65536 : ℝ))) (2224585233/12500000000 : ℝ) (88983409323/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8437/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2224585233/12500000000 : ℝ) (88983409323/500000000000 : ℝ) (14724585233/25000000000 : ℝ) (588983409323/1000000000000 : ℝ) (210930568339/500000000000 : ℝ) (210930568343/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8437/65536 : ℝ))) 1 (14724585233/25000000000 : ℝ) (588983409323/1000000000000 : ℝ) (210930568339/500000000000 : ℝ) (210930568343/500000000000 : ℝ) (505422272999/1000000000000 : ℝ) (101084454601/200000000000 : ℝ) (249233430011/500000000000 : ℝ) (498466860029/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8437/65536 : ℝ))) 2 (505422272999/1000000000000 : ℝ) (101084454601/200000000000 : ℝ) (249233430011/500000000000 : ℝ) (498466860029/1000000000000 : ℝ) (50194456651/100000000000 : ℝ) (501944566517/1000000000000 : ℝ) (250966259389/500000000000 : ℝ) (100386503757/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8437/65536 : ℝ))) 3 (50194456651/100000000000 : ℝ) (501944566517/1000000000000 : ℝ) (250966259389/500000000000 : ℝ) (100386503757/200000000000 : ℝ) (125484635661/250000000000 : ℝ) (501938542651/1000000000000 : ℝ) (501938542607/1000000000000 : ℝ) (100387708523/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8437/65536 : ℝ))) 4 (125484635661/250000000000 : ℝ) (501938542651/1000000000000 : ℝ) (501938542607/1000000000000 : ℝ) (100387708523/200000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8437/65536 : ℝ))) 5 (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8437/65536 : ℝ))) 6 (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8437/65536 : ℝ))) 7 (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8437/65536 : ℝ)) hmem 8 (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8437/65536 : ℝ))) hcmem 8 (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8437/65536 : ℝ)) (496001094431/500000000000 : ℝ) (496001094433/500000000000 : ℝ) (4015508341/8000000000 : ℝ) (501938542633/1000000000000 : ℝ) (198699969587/250000000000 : ℝ) (158959975673/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1315_exp_lower
  have heNumeric : (513725969099/250000000000 : ℝ)/4 ≤ Real.exp (-8525635708697/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725969099/250000000000 : ℝ)/4 ≤ Real.exp ((33747/262144 : ℝ)-(158959975673/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33747/262144 : ℝ) (8437/65536 : ℝ) (158959975673/200000000000 : ℝ) (513725969099/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1316; no trusted numerical premise.
theorem cover8_leaf1316_exp_radius : (199598084949811/200000000000000 : ℝ) ≤ Real.exp ((-33749/2097152 : ℝ)/8) ∧ Real.exp ((-33749/2097152 : ℝ)/8) ≤ (997990424749055001/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33749/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1316_exp_lower : (920113581403500041/1000000000000000000 : ℝ) ≤ Real.exp ((-10657044289547/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657044289547/16000000000000 : ℝ)/8) ≤ (460056790701750021/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657044289547/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1316_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (16439231367/8000000000 : ℝ) ≤ 4*Real.exp (8437/65536 : ℝ)*Real.exp (-mu (radius 8 (33749/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (16439231367/8000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33749/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1316_exp_radius
  have hrNumeric : (492018009831/500000000000 : ℝ) ≤ Real.exp (-33749/2097152 : ℝ) ∧ Real.exp (-33749/2097152 : ℝ) ≤ (984036019663/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492018009831/500000000000 : ℝ) ≤ (radius 8 (33749/262144 : ℝ)) ∧ (radius 8 (33749/262144 : ℝ)) ≤ (984036019663/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33749/262144 : ℝ)) (492018009831/500000000000 : ℝ) (984036019663/1000000000000 : ℝ) (88984706559/500000000000 : ℝ) (284751061/1600000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33749/262144 : ℝ)) (492018009831/500000000000 : ℝ) (984036019663/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33749/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492018009831/500000000000 : ℝ) (984036019663/1000000000000 : ℝ) (992018009831/1000000000000 : ℝ) (124002251229/125000000000 : ℝ) (495992948453/500000000000 : ℝ) (247996474227/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33749/262144 : ℝ)) 1 (992018009831/1000000000000 : ℝ) (124002251229/125000000000 : ℝ) (495992948453/500000000000 : ℝ) (247996474227/250000000000 : ℝ) (124000244171/125000000000 : ℝ) (99200195337/100000000000 : ℝ) (496000976619/500000000000 : ℝ) (992001953241/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33749/262144 : ℝ)) 2 (124000244171/125000000000 : ℝ) (99200195337/100000000000 : ℝ) (496000976619/500000000000 : ℝ) (992001953241/1000000000000 : ℝ) (992001953303/1000000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33749/262144 : ℝ)) 3 (992001953303/1000000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33749/262144 : ℝ)) 4 (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33749/262144 : ℝ)) 5 (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33749/262144 : ℝ)) 6 (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33749/262144 : ℝ)) 7 (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33749/262144 : ℝ))) (88984706559/500000000000 : ℝ) (284751061/1600000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33749/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88984706559/500000000000 : ℝ) (284751061/1600000000 : ℝ) (588984706559/1000000000000 : ℝ) (588984706563/1000000000000 : ℝ) (84372842341/200000000000 : ℝ) (210932105857/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33749/262144 : ℝ))) 1 (588984706559/1000000000000 : ℝ) (588984706563/1000000000000 : ℝ) (84372842341/200000000000 : ℝ) (210932105857/500000000000 : ℝ) (126356114783/250000000000 : ℝ) (505424459139/1000000000000 : ℝ) (124617306417/250000000000 : ℝ) (124617306419/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33749/262144 : ℝ))) 2 (126356114783/250000000000 : ℝ) (505424459139/1000000000000 : ℝ) (124617306417/250000000000 : ℝ) (124617306419/250000000000 : ℝ) (627433553/1250000000 : ℝ) (62743355301/125000000000 : ℝ) (31370924709/62500000000 : ℝ) (62741849419/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33749/262144 : ℝ))) 3 (627433553/1250000000 : ℝ) (62743355301/125000000000 : ℝ) (31370924709/62500000000 : ℝ) (62741849419/125000000000 : ℝ) (62742602359/125000000000 : ℝ) (1568565059/3125000000 : ℝ) (100388163767/200000000000 : ℝ) (125485204711/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33749/262144 : ℝ))) 4 (62742602359/125000000000 : ℝ) (1568565059/3125000000 : ℝ) (100388163767/200000000000 : ℝ) (125485204711/250000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33749/262144 : ℝ))) 5 (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33749/262144 : ℝ))) 6 (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33749/262144 : ℝ))) 7 (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33749/262144 : ℝ)) hmem 8 (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33749/262144 : ℝ))) hcmem 8 (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33749/262144 : ℝ)) (496000976651/500000000000 : ℝ) (496000976653/500000000000 : ℝ) (501940818853/1000000000000 : ℝ) (250970409431/500000000000 : ℝ) (794803671399/1000000000000 : ℝ) (794803671417/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1316_exp_lower
  have heNumeric : (16439231367/8000000000 : ℝ)/4 ≤ Real.exp (-10657044289547/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (16439231367/8000000000 : ℝ)/4 ≤ Real.exp ((8437/65536 : ℝ)-(794803671417/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8437/65536 : ℝ) (33749/262144 : ℝ) (794803671417/1000000000000 : ℝ) (16439231367/8000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1317; no trusted numerical premise.
theorem cover8_leaf1317_exp_radius : (997990365264192017/1000000000000000000 : ℝ) ≤ Real.exp ((-16875/1048576 : ℝ)/8) ∧ Real.exp ((-16875/1048576 : ℝ)/8) ≤ (498995182632096009/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16875/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1317_exp_lower : (460056791950761977/500000000000000000 : ℝ) ≤ Real.exp ((-8525635153631/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525635153631/12800000000000 : ℝ)/8) ≤ (184022716780304791/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525635153631/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1317_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451982753/500000000000 : ℝ) ≤ 4*Real.exp (33749/262144 : ℝ)*Real.exp (-mu (radius 8 (16875/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451982753/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16875/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1317_exp_radius
  have hrNumeric : (984035550437/1000000000000 : ℝ) ≤ Real.exp (-16875/1048576 : ℝ) ∧ Real.exp (-16875/1048576 : ℝ) ≤ (492017775219/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984035550437/1000000000000 : ℝ) ≤ (radius 8 (16875/131072 : ℝ)) ∧ (radius 8 (16875/131072 : ℝ)) ≤ (492017775219/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16875/131072 : ℝ)) (984035550437/1000000000000 : ℝ) (492017775219/500000000000 : ℝ) (177972007557/1000000000000 : ℝ) (44493001891/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16875/131072 : ℝ)) (984035550437/1000000000000 : ℝ) (492017775219/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16875/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984035550437/1000000000000 : ℝ) (492017775219/500000000000 : ℝ) (496008887609/500000000000 : ℝ) (992017775219/1000000000000 : ℝ) (495992830199/500000000000 : ℝ) (2479964151/2500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16875/131072 : ℝ)) 1 (496008887609/500000000000 : ℝ) (992017775219/1000000000000 : ℝ) (495992830199/500000000000 : ℝ) (2479964151/2500000000 : ℝ) (62000107363/62500000000 : ℝ) (99200171781/100000000000 : ℝ) (496000858839/500000000000 : ℝ) (12400021471/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16875/131072 : ℝ)) 2 (62000107363/62500000000 : ℝ) (99200171781/100000000000 : ℝ) (496000858839/500000000000 : ℝ) (12400021471/12500000000 : ℝ) (992001717743/1000000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16875/131072 : ℝ)) 3 (992001717743/1000000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16875/131072 : ℝ)) 4 (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16875/131072 : ℝ)) 5 (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16875/131072 : ℝ)) 6 (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16875/131072 : ℝ)) 7 (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16875/131072 : ℝ))) (177972007557/1000000000000 : ℝ) (44493001891/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16875/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177972007557/1000000000000 : ℝ) (44493001891/250000000000 : ℝ) (294493001889/500000000000 : ℝ) (294493001891/500000000000 : ℝ) (421867286663/1000000000000 : ℝ) (421867286673/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16875/131072 : ℝ))) 1 (294493001889/500000000000 : ℝ) (294493001891/500000000000 : ℝ) (421867286663/1000000000000 : ℝ) (421867286673/1000000000000 : ℝ) (25271332261/50000000000 : ℝ) (126356661307/250000000000 : ℝ) (498471591263/1000000000000 : ℝ) (498471591271/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16875/131072 : ℝ))) 2 (25271332261/50000000000 : ℝ) (126356661307/250000000000 : ℝ) (498471591263/1000000000000 : ℝ) (498471591271/1000000000000 : ℝ) (501949118241/1000000000000 : ℝ) (2007796473/4000000000 : ℝ) (250968535931/500000000000 : ℝ) (501937071871/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16875/131072 : ℝ))) 3 (501949118241/1000000000000 : ℝ) (2007796473/4000000000 : ℝ) (250968535931/500000000000 : ℝ) (501937071871/1000000000000 : ℝ) (501943095051/1000000000000 : ℝ) (501943095061/1000000000000 : ℝ) (100388619003/200000000000 : ℝ) (20077723801/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16875/131072 : ℝ))) 4 (501943095051/1000000000000 : ℝ) (501943095061/1000000000000 : ℝ) (100388619003/200000000000 : ℝ) (20077723801/40000000000 : ℝ) (501943095033/1000000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16875/131072 : ℝ))) 5 (501943095033/1000000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16875/131072 : ℝ))) 6 (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16875/131072 : ℝ))) 7 (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16875/131072 : ℝ)) hmem 8 (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16875/131072 : ℝ))) hcmem 8 (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16875/131072 : ℝ)) (496000858871/500000000000 : ℝ) (198400343549/200000000000 : ℝ) (62742886879/125000000000 : ℝ) (501943095043/1000000000000 : ℝ) (397403732187/500000000000 : ℝ) (158961492879/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1317_exp_lower
  have heNumeric : (1027451982753/500000000000 : ℝ)/4 ≤ Real.exp (-8525635153631/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451982753/500000000000 : ℝ)/4 ≤ Real.exp ((33749/262144 : ℝ)-(158961492879/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33749/262144 : ℝ) (16875/131072 : ℝ) (158961492879/200000000000 : ℝ) (1027451982753/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1318; no trusted numerical premise.
theorem cover8_leaf1318_exp_radius : (498995152889666289/500000000000000000 : ℝ) ≤ Real.exp ((-33751/2097152 : ℝ)/8) ∧ Real.exp ((-33751/2097152 : ℝ)/8) ≤ (997990305779332579/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33751/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1318_exp_lower : (898548424226957/976562500000000 : ℝ) ≤ Real.exp ((-21314087186597/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314087186597/32000000000000 : ℝ)/8) ≤ (920113586408403969/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314087186597/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1318_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980802059/200000000000 : ℝ) ≤ 4*Real.exp (16875/131072 : ℝ)*Real.exp (-mu (radius 8 (33751/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980802059/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33751/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1318_exp_radius
  have hrNumeric : (246008770303/250000000000 : ℝ) ≤ Real.exp (-33751/2097152 : ℝ) ∧ Real.exp (-33751/2097152 : ℝ) ≤ (984035081213/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246008770303/250000000000 : ℝ) ≤ (radius 8 (33751/262144 : ℝ)) ∧ (radius 8 (33751/262144 : ℝ)) ≤ (984035081213/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33751/262144 : ℝ)) (246008770303/250000000000 : ℝ) (984035081213/1000000000000 : ℝ) (88987300979/500000000000 : ℝ) (44493650491/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33751/262144 : ℝ)) (246008770303/250000000000 : ℝ) (984035081213/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33751/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246008770303/250000000000 : ℝ) (984035081213/1000000000000 : ℝ) (496008770303/500000000000 : ℝ) (992017540607/1000000000000 : ℝ) (99198542389/100000000000 : ℝ) (247996355973/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33751/262144 : ℝ)) 1 (496008770303/500000000000 : ℝ) (992017540607/1000000000000 : ℝ) (99198542389/100000000000 : ℝ) (247996355973/250000000000 : ℝ) (124000185281/125000000000 : ℝ) (3968005929/4000000000 : ℝ) (496000741059/500000000000 : ℝ) (24800037053/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33751/262144 : ℝ)) 2 (124000185281/125000000000 : ℝ) (3968005929/4000000000 : ℝ) (496000741059/500000000000 : ℝ) (24800037053/25000000000 : ℝ) (992001482183/1000000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33751/262144 : ℝ)) 3 (992001482183/1000000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33751/262144 : ℝ)) 4 (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33751/262144 : ℝ)) 5 (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33751/262144 : ℝ)) 6 (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33751/262144 : ℝ)) 7 (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33751/262144 : ℝ))) (88987300979/500000000000 : ℝ) (44493650491/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33751/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88987300979/500000000000 : ℝ) (44493650491/250000000000 : ℝ) (588987300979/1000000000000 : ℝ) (294493650491/500000000000 : ℝ) (210935180777/500000000000 : ℝ) (210935180781/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33751/262144 : ℝ))) 1 (588987300979/1000000000000 : ℝ) (294493650491/500000000000 : ℝ) (210935180777/500000000000 : ℝ) (210935180781/500000000000 : ℝ) (252714415633/500000000000 : ℝ) (63178603909/125000000000 : ℝ) (249236978403/500000000000 : ℝ) (498473956813/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33751/262144 : ℝ))) 2 (252714415633/500000000000 : ℝ) (63178603909/125000000000 : ℝ) (249236978403/500000000000 : ℝ) (498473956813/1000000000000 : ℝ) (125487848509/250000000000 : ℝ) (501951394043/1000000000000 : ℝ) (501939348333/1000000000000 : ℝ) (25096967417/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33751/262144 : ℝ))) 3 (125487848509/250000000000 : ℝ) (501951394043/1000000000000 : ℝ) (501939348333/1000000000000 : ℝ) (25096967417/50000000000 : ℝ) (31371585699/62500000000 : ℝ) (62743171399/125000000000 : ℝ) (125486342787/250000000000 : ℝ) (125486342789/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33751/262144 : ℝ))) 4 (31371585699/62500000000 : ℝ) (62743171399/125000000000 : ℝ) (125486342787/250000000000 : ℝ) (125486342789/250000000000 : ℝ) (250972685583/500000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33751/262144 : ℝ))) 5 (250972685583/500000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33751/262144 : ℝ))) 6 (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33751/262144 : ℝ))) 7 (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33751/262144 : ℝ)) hmem 8 (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33751/262144 : ℝ))) hcmem 8 (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33751/262144 : ℝ)) (496000741091/500000000000 : ℝ) (198400296437/200000000000 : ℝ) (100389074233/200000000000 : ℝ) (250972685587/500000000000 : ℝ) (397405628639/500000000000 : ℝ) (49675703581/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1318_exp_lower
  have heNumeric : (410980802059/200000000000 : ℝ)/4 ≤ Real.exp (-21314087186597/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980802059/200000000000 : ℝ)/4 ≤ Real.exp ((16875/131072 : ℝ)-(49675703581/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16875/131072 : ℝ) (33751/262144 : ℝ) (49675703581/62500000000 : ℝ) (410980802059/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1319; no trusted numerical premise.
theorem cover8_leaf1319_exp_radius : (498995123147238343/500000000000000000 : ℝ) ≤ Real.exp ((-4219/262144 : ℝ)/8) ∧ Real.exp ((-4219/262144 : ℝ)/8) ≤ (997990246294476687/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4219/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1319_exp_lower : (460056794462300069/500000000000000000 : ℝ) ≤ Real.exp ((-42628172973049/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628172973049/64000000000000 : ℝ)/8) ≤ (920113588924600139/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628172973049/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1319_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904055251/1000000000000 : ℝ) ≤ 4*Real.exp (33751/262144 : ℝ)*Real.exp (-mu (radius 8 (4219/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904055251/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4219/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1319_exp_radius
  have hrNumeric : (246008652997/250000000000 : ℝ) ≤ Real.exp (-4219/262144 : ℝ) ∧ Real.exp (-4219/262144 : ℝ) ≤ (984034611989/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246008652997/250000000000 : ℝ) ≤ (radius 8 (4219/32768 : ℝ)) ∧ (radius 8 (4219/32768 : ℝ)) ≤ (984034611989/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4219/32768 : ℝ)) (246008652997/250000000000 : ℝ) (984034611989/1000000000000 : ℝ) (177977196313/1000000000000 : ℝ) (1112357477/6250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4219/32768 : ℝ)) (246008652997/250000000000 : ℝ) (984034611989/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4219/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246008652997/250000000000 : ℝ) (984034611989/1000000000000 : ℝ) (496008652997/500000000000 : ℝ) (198403461199/200000000000 : ℝ) (991985187383/1000000000000 : ℝ) (123998148423/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4219/32768 : ℝ)) 1 (496008652997/500000000000 : ℝ) (198403461199/200000000000 : ℝ) (991985187383/1000000000000 : ℝ) (123998148423/125000000000 : ℝ) (31000038959/31250000000 : ℝ) (99200124669/100000000000 : ℝ) (496000623279/500000000000 : ℝ) (6200007791/6250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4219/32768 : ℝ)) 2 (31000038959/31250000000 : ℝ) (99200124669/100000000000 : ℝ) (496000623279/500000000000 : ℝ) (6200007791/6250000000 : ℝ) (992001246623/1000000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4219/32768 : ℝ)) 3 (992001246623/1000000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4219/32768 : ℝ)) 4 (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4219/32768 : ℝ)) 5 (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4219/32768 : ℝ)) 6 (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4219/32768 : ℝ)) 7 (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4219/32768 : ℝ))) (177977196313/1000000000000 : ℝ) (1112357477/6250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4219/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177977196313/1000000000000 : ℝ) (1112357477/6250000000 : ℝ) (147247149539/250000000000 : ℝ) (7362357477/12500000000 : ℝ) (26367089773/62500000000 : ℝ) (421873436377/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4219/32768 : ℝ))) 1 (147247149539/250000000000 : ℝ) (7362357477/12500000000 : ℝ) (26367089773/62500000000 : ℝ) (421873436377/1000000000000 : ℝ) (252715508631/500000000000 : ℝ) (505431017269/1000000000000 : ℝ) (498476322291/1000000000000 : ℝ) (498476322299/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4219/32768 : ℝ))) 2 (252715508631/500000000000 : ℝ) (505431017269/1000000000000 : ℝ) (498476322291/1000000000000 : ℝ) (498476322299/1000000000000 : ℝ) (31372104361/62500000000 : ℝ) (62744208723/125000000000 : ℝ) (501941624749/1000000000000 : ℝ) (250970812379/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4219/32768 : ℝ))) 3 (31372104361/62500000000 : ℝ) (62744208723/125000000000 : ℝ) (501941624749/1000000000000 : ℝ) (250970812379/500000000000 : ℝ) (250973823631/500000000000 : ℝ) (501947647271/1000000000000 : ℝ) (250973823613/500000000000 : ℝ) (100389529447/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4219/32768 : ℝ))) 4 (250973823631/500000000000 : ℝ) (501947647271/1000000000000 : ℝ) (250973823613/500000000000 : ℝ) (100389529447/200000000000 : ℝ) (125486911811/250000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4219/32768 : ℝ))) 5 (125486911811/250000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4219/32768 : ℝ))) 6 (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4219/32768 : ℝ))) 7 (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4219/32768 : ℝ)) hmem 8 (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4219/32768 : ℝ))) hcmem 8 (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4219/32768 : ℝ)) (496000623311/500000000000 : ℝ) (7936009973/8000000000 : ℝ) (501947647243/1000000000000 : ℝ) (501947647253/1000000000000 : ℝ) (794815050097/1000000000000 : ℝ) (198703762529/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1319_exp_lower
  have heNumeric : (2054904055251/1000000000000 : ℝ)/4 ≤ Real.exp (-42628172973049/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904055251/1000000000000 : ℝ)/4 ≤ Real.exp ((33751/262144 : ℝ)-(198703762529/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33751/262144 : ℝ) (4219/32768 : ℝ) (198703762529/250000000000 : ℝ) (2054904055251/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1320; no trusted numerical premise.
theorem cover8_leaf1320_exp_radius : (997990186809624339/1000000000000000000 : ℝ) ≤ Real.exp ((-33753/2097152 : ℝ)/8) ∧ Real.exp ((-33753/2097152 : ℝ)/8) ≤ (49899509340481217/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33753/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1320_exp_lower : (460056795724768697/500000000000000000 : ℝ) ≤ Real.exp ((-1065704289201/1600000000000 : ℝ)/8) ∧ Real.exp ((-1065704289201/1600000000000 : ℝ)/8) ≤ (184022718289907479/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065704289201/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1320_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904100363/1000000000000 : ℝ) ≤ 4*Real.exp (4219/32768 : ℝ)*Real.exp (-mu (radius 8 (33753/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904100363/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33753/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1320_exp_radius
  have hrNumeric : (246008535691/250000000000 : ℝ) ≤ Real.exp (-33753/2097152 : ℝ) ∧ Real.exp (-33753/2097152 : ℝ) ≤ (196806828553/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246008535691/250000000000 : ℝ) ≤ (radius 8 (33753/262144 : ℝ)) ∧ (radius 8 (33753/262144 : ℝ)) ≤ (196806828553/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33753/262144 : ℝ)) (246008535691/250000000000 : ℝ) (196806828553/200000000000 : ℝ) (17797979063/100000000000 : ℝ) (44494947659/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33753/262144 : ℝ)) (246008535691/250000000000 : ℝ) (196806828553/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33753/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246008535691/250000000000 : ℝ) (196806828553/200000000000 : ℝ) (496008535691/500000000000 : ℝ) (992017071383/1000000000000 : ℝ) (7935879607/8000000000 : ℝ) (991984950877/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33753/262144 : ℝ)) 1 (496008535691/500000000000 : ℝ) (992017071383/1000000000000 : ℝ) (7935879607/8000000000 : ℝ) (991984950877/1000000000000 : ℝ) (124000126391/125000000000 : ℝ) (99200101113/100000000000 : ℝ) (496000505499/500000000000 : ℝ) (992001011/1000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33753/262144 : ℝ)) 2 (124000126391/125000000000 : ℝ) (99200101113/100000000000 : ℝ) (496000505499/500000000000 : ℝ) (992001011/1000000000 : ℝ) (992001011063/1000000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33753/262144 : ℝ)) 3 (992001011063/1000000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33753/262144 : ℝ)) 4 (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33753/262144 : ℝ)) 5 (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33753/262144 : ℝ)) 6 (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33753/262144 : ℝ)) 7 (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33753/262144 : ℝ))) (17797979063/100000000000 : ℝ) (44494947659/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33753/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17797979063/100000000000 : ℝ) (44494947659/250000000000 : ℝ) (117797979063/200000000000 : ℝ) (294494947659/500000000000 : ℝ) (210938255557/500000000000 : ℝ) (210938255561/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33753/262144 : ℝ))) 1 (117797979063/200000000000 : ℝ) (294494947659/500000000000 : ℝ) (210938255557/500000000000 : ℝ) (210938255561/500000000000 : ℝ) (252716601607/500000000000 : ℝ) (25271660161/50000000000 : ℝ) (19939147509/40000000000 : ℝ) (124619671933/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33753/262144 : ℝ))) 2 (252716601607/500000000000 : ℝ) (25271660161/50000000000 : ℝ) (19939147509/40000000000 : ℝ) (124619671933/250000000000 : ℝ) (501955945469/1000000000000 : ℝ) (125488986369/250000000000 : ℝ) (501943901119/1000000000000 : ℝ) (250971950563/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33753/262144 : ℝ))) 3 (501955945469/1000000000000 : ℝ) (125488986369/250000000000 : ℝ) (501943901119/1000000000000 : ℝ) (250971950563/500000000000 : ℝ) (250974961647/500000000000 : ℝ) (501949923301/1000000000000 : ℝ) (501949923257/1000000000000 : ℝ) (100389984653/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33753/262144 : ℝ))) 4 (250974961647/500000000000 : ℝ) (501949923301/1000000000000 : ℝ) (501949923257/1000000000000 : ℝ) (100389984653/200000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33753/262144 : ℝ))) 5 (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33753/262144 : ℝ))) 6 (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33753/262144 : ℝ))) 7 (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33753/262144 : ℝ)) hmem 8 (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33753/262144 : ℝ))) hcmem 8 (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33753/262144 : ℝ)) (496000505531/500000000000 : ℝ) (198400202213/200000000000 : ℝ) (20077996931/40000000000 : ℝ) (501949923283/1000000000000 : ℝ) (198704710711/250000000000 : ℝ) (39740942143/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1320_exp_lower
  have heNumeric : (2054904100363/1000000000000 : ℝ)/4 ≤ Real.exp (-1065704289201/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904100363/1000000000000 : ℝ)/4 ≤ Real.exp ((4219/32768 : ℝ)-(39740942143/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4219/32768 : ℝ) (33753/262144 : ℝ) (39740942143/50000000000 : ℝ) (2054904100363/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1321; no trusted numerical premise.
theorem cover8_leaf1321_exp_radius : (498995063662387769/500000000000000000 : ℝ) ≤ Real.exp ((-16877/1048576 : ℝ)/8) ∧ Real.exp ((-16877/1048576 : ℝ)/8) ≤ (997990127324775539/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16877/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1321_exp_lower : (460056796991320333/500000000000000000 : ℝ) ≤ Real.exp ((-42628170158487/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628170158487/64000000000000 : ℝ)/8) ≤ (920113593982640667/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628170158487/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1321_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745207281/50000000000 : ℝ) ≤ 4*Real.exp (33753/262144 : ℝ)*Real.exp (-mu (radius 8 (16877/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (102745207281/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16877/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1321_exp_radius
  have hrNumeric : (49201683677/50000000000 : ℝ) ≤ Real.exp (-16877/1048576 : ℝ) ∧ Real.exp (-16877/1048576 : ℝ) ≤ (984033673541/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49201683677/50000000000 : ℝ) ≤ (radius 8 (16877/131072 : ℝ)) ∧ (radius 8 (16877/131072 : ℝ)) ≤ (984033673541/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16877/131072 : ℝ)) (49201683677/50000000000 : ℝ) (984033673541/1000000000000 : ℝ) (177982384907/1000000000000 : ℝ) (88991192457/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16877/131072 : ℝ)) (49201683677/50000000000 : ℝ) (984033673541/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16877/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49201683677/50000000000 : ℝ) (984033673541/1000000000000 : ℝ) (99201683677/100000000000 : ℝ) (992016836771/1000000000000 : ℝ) (7749880581/7812500000 : ℝ) (991984714369/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16877/131072 : ℝ)) 1 (99201683677/100000000000 : ℝ) (992016836771/1000000000000 : ℝ) (7749880581/7812500000 : ℝ) (991984714369/1000000000000 : ℝ) (992000775569/1000000000000 : ℝ) (99200077557/100000000000 : ℝ) (496000387719/500000000000 : ℝ) (12400009693/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16877/131072 : ℝ)) 2 (992000775569/1000000000000 : ℝ) (99200077557/100000000000 : ℝ) (496000387719/500000000000 : ℝ) (12400009693/12500000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16877/131072 : ℝ)) 3 (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16877/131072 : ℝ)) 4 (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16877/131072 : ℝ)) 5 (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16877/131072 : ℝ)) 6 (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16877/131072 : ℝ)) 7 (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16877/131072 : ℝ))) (177982384907/1000000000000 : ℝ) (88991192457/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16877/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177982384907/1000000000000 : ℝ) (88991192457/500000000000 : ℝ) (588991192453/1000000000000 : ℝ) (588991192457/1000000000000 : ℝ) (42187958579/100000000000 : ℝ) (2109397929/5000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16877/131072 : ℝ))) 1 (588991192453/1000000000000 : ℝ) (588991192457/1000000000000 : ℝ) (42187958579/100000000000 : ℝ) (2109397929/5000000000 : ℝ) (505435389121/1000000000000 : ℝ) (505435389129/1000000000000 : ℝ) (249240526553/500000000000 : ℝ) (249240526557/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16877/131072 : ℝ))) 2 (505435389121/1000000000000 : ℝ) (505435389129/1000000000000 : ℝ) (249240526553/500000000000 : ℝ) (249240526557/500000000000 : ℝ) (501958221113/1000000000000 : ℝ) (250979110561/500000000000 : ℝ) (501946177439/1000000000000 : ℝ) (62743272181/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16877/131072 : ℝ))) 3 (501958221113/1000000000000 : ℝ) (250979110561/500000000000 : ℝ) (501946177439/1000000000000 : ℝ) (62743272181/125000000000 : ℝ) (125488049819/250000000000 : ℝ) (100390439857/200000000000 : ℝ) (501952199239/1000000000000 : ℝ) (501952199249/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16877/131072 : ℝ))) 4 (125488049819/250000000000 : ℝ) (100390439857/200000000000 : ℝ) (501952199239/1000000000000 : ℝ) (501952199249/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16877/131072 : ℝ))) 5 (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16877/131072 : ℝ))) 6 (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16877/131072 : ℝ))) 7 (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16877/131072 : ℝ)) hmem 8 (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16877/131072 : ℝ))) hcmem 8 (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16877/131072 : ℝ)) (992000775503/1000000000000 : ℝ) (198400155101/200000000000 : ℝ) (501952199257/1000000000000 : ℝ) (501952199267/1000000000000 : ℝ) (397411317757/500000000000 : ℝ) (794822635533/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1321_exp_lower
  have heNumeric : (102745207281/50000000000 : ℝ)/4 ≤ Real.exp (-42628170158487/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745207281/50000000000 : ℝ)/4 ≤ Real.exp ((33753/262144 : ℝ)-(794822635533/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33753/262144 : ℝ) (16877/131072 : ℝ) (794822635533/1000000000000 : ℝ) (102745207281/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1322; no trusted numerical premise.
theorem cover8_leaf1322_exp_radius : (498995033919965141/500000000000000000 : ℝ) ≤ Real.exp ((-33755/2097152 : ℝ)/8) ∧ Real.exp ((-33755/2097152 : ℝ)/8) ≤ (997990067839930283/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33755/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1322_exp_lower : (920113596524600037/1000000000000000000 : ℝ) ≤ Real.exp ((-21314084372003/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314084372003/32000000000000 : ℝ)/8) ≤ (460056798262300019/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314084372003/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1322_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726047759/250000000000 : ℝ) ≤ 4*Real.exp (16877/131072 : ℝ)*Real.exp (-mu (radius 8 (33755/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513726047759/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33755/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1322_exp_radius
  have hrNumeric : (246008301079/250000000000 : ℝ) ≤ Real.exp (-33755/2097152 : ℝ) ∧ Real.exp (-33755/2097152 : ℝ) ≤ (984033204317/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246008301079/250000000000 : ℝ) ≤ (radius 8 (33755/262144 : ℝ)) ∧ (radius 8 (33755/262144 : ℝ)) ≤ (984033204317/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33755/262144 : ℝ)) (246008301079/250000000000 : ℝ) (984033204317/1000000000000 : ℝ) (88992489573/500000000000 : ℝ) (11124061197/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33755/262144 : ℝ)) (246008301079/250000000000 : ℝ) (984033204317/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33755/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246008301079/250000000000 : ℝ) (984033204317/1000000000000 : ℝ) (496008301079/500000000000 : ℝ) (992016602159/1000000000000 : ℝ) (49599223893/50000000000 : ℝ) (991984477861/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33755/262144 : ℝ)) 1 (496008301079/500000000000 : ℝ) (992016602159/1000000000000 : ℝ) (49599223893/50000000000 : ℝ) (991984477861/1000000000000 : ℝ) (992000540009/1000000000000 : ℝ) (99200054001/100000000000 : ℝ) (496000269939/500000000000 : ℝ) (24800013497/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33755/262144 : ℝ)) 2 (992000540009/1000000000000 : ℝ) (99200054001/100000000000 : ℝ) (496000269939/500000000000 : ℝ) (24800013497/25000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33755/262144 : ℝ)) 3 (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33755/262144 : ℝ)) 4 (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33755/262144 : ℝ)) 5 (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33755/262144 : ℝ)) 6 (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33755/262144 : ℝ)) 7 (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33755/262144 : ℝ))) (88992489573/500000000000 : ℝ) (11124061197/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33755/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88992489573/500000000000 : ℝ) (11124061197/62500000000 : ℝ) (588992489573/1000000000000 : ℝ) (73624061197/125000000000 : ℝ) (421882660399/1000000000000 : ℝ) (421882660407/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33755/262144 : ℝ))) 1 (588992489573/1000000000000 : ℝ) (73624061197/125000000000 : ℝ) (421882660399/1000000000000 : ℝ) (421882660407/1000000000000 : ℝ) (252718787493/500000000000 : ℝ) (31589848437/62500000000 : ℝ) (124620854609/250000000000 : ℝ) (498483418443/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33755/262144 : ℝ))) 2 (252718787493/500000000000 : ℝ) (31589848437/62500000000 : ℝ) (124620854609/250000000000 : ℝ) (498483418443/1000000000000 : ℝ) (501960496711/1000000000000 : ℝ) (250980248359/500000000000 : ℝ) (501948453713/1000000000000 : ℝ) (12548711343/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33755/262144 : ℝ))) 3 (501960496711/1000000000000 : ℝ) (250980248359/500000000000 : ℝ) (501948453713/1000000000000 : ℝ) (12548711343/25000000000 : ℝ) (125488618803/250000000000 : ℝ) (501954475219/1000000000000 : ℝ) (20078179007/40000000000 : ℝ) (501954475183/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33755/262144 : ℝ))) 4 (125488618803/250000000000 : ℝ) (501954475219/1000000000000 : ℝ) (20078179007/40000000000 : ℝ) (501954475183/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33755/262144 : ℝ))) 5 (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33755/262144 : ℝ))) 6 (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33755/262144 : ℝ))) 7 (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33755/262144 : ℝ)) hmem 8 (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33755/262144 : ℝ))) hcmem 8 (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33755/262144 : ℝ)) (992000539943/1000000000000 : ℝ) (198400107989/200000000000 : ℝ) (501954475193/1000000000000 : ℝ) (501954475201/1000000000000 : ℝ) (794826428113/1000000000000 : ℝ) (794826428129/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1322_exp_lower
  have heNumeric : (513726047759/250000000000 : ℝ)/4 ≤ Real.exp (-21314084372003/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726047759/250000000000 : ℝ)/4 ≤ Real.exp ((16877/131072 : ℝ)-(794826428129/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16877/131072 : ℝ) (33755/262144 : ℝ) (794826428129/1000000000000 : ℝ) (513726047759/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1323; no trusted numerical premise.
theorem cover8_leaf1323_exp_radius : (249497502088772143/250000000000000000 : ℝ) ≤ Real.exp ((-8439/524288 : ℝ)/8) ∧ Real.exp ((-8439/524288 : ℝ)/8) ≤ (997990008355088573/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8439/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1323_exp_lower : (920113599074955453/1000000000000000000 : ℝ) ≤ Real.exp ((-42628167324853/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628167324853/64000000000000 : ℝ)/8) ≤ (460056799537477727/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628167324853/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1323_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452118301/500000000000 : ℝ) ≤ 4*Real.exp (33755/262144 : ℝ)*Real.exp (-mu (radius 8 (8439/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452118301/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8439/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1323_exp_radius
  have hrNumeric : (246008183773/250000000000 : ℝ) ≤ Real.exp (-8439/524288 : ℝ) ∧ Real.exp (-8439/524288 : ℝ) ≤ (984032735093/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246008183773/250000000000 : ℝ) ≤ (radius 8 (8439/65536 : ℝ)) ∧ (radius 8 (8439/65536 : ℝ)) ≤ (984032735093/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8439/65536 : ℝ)) (246008183773/250000000000 : ℝ) (984032735093/1000000000000 : ℝ) (35597514669/200000000000 : ℝ) (177987573351/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8439/65536 : ℝ)) (246008183773/250000000000 : ℝ) (984032735093/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8439/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246008183773/250000000000 : ℝ) (984032735093/1000000000000 : ℝ) (496008183773/500000000000 : ℝ) (992016367547/1000000000000 : ℝ) (123998030169/125000000000 : ℝ) (495992120677/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8439/65536 : ℝ)) 1 (496008183773/500000000000 : ℝ) (992016367547/1000000000000 : ℝ) (123998030169/125000000000 : ℝ) (495992120677/500000000000 : ℝ) (992000304449/1000000000000 : ℝ) (992000304451/1000000000000 : ℝ) (496000152159/500000000000 : ℝ) (992000304321/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8439/65536 : ℝ)) 2 (992000304449/1000000000000 : ℝ) (992000304451/1000000000000 : ℝ) (496000152159/500000000000 : ℝ) (992000304321/1000000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8439/65536 : ℝ)) 3 (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8439/65536 : ℝ)) 4 (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8439/65536 : ℝ)) 5 (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8439/65536 : ℝ)) 6 (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8439/65536 : ℝ)) 7 (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8439/65536 : ℝ))) (35597514669/200000000000 : ℝ) (177987573351/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8439/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35597514669/200000000000 : ℝ) (177987573351/1000000000000 : ℝ) (36812111667/62500000000 : ℝ) (147248446669/250000000000 : ℝ) (210942867469/500000000000 : ℝ) (421885734947/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8439/65536 : ℝ))) 1 (36812111667/62500000000 : ℝ) (147248446669/250000000000 : ℝ) (210942867469/500000000000 : ℝ) (421885734947/1000000000000 : ℝ) (101087952161/200000000000 : ℝ) (126359940203/250000000000 : ℝ) (498485783713/1000000000000 : ℝ) (498485783721/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8439/65536 : ℝ))) 2 (101087952161/200000000000 : ℝ) (126359940203/250000000000 : ℝ) (498485783713/1000000000000 : ℝ) (498485783721/1000000000000 : ℝ) (501962772259/1000000000000 : ℝ) (501962772267/1000000000000 : ℝ) (501950729937/1000000000000 : ℝ) (100390145989/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8439/65536 : ℝ))) 3 (501962772259/1000000000000 : ℝ) (501962772267/1000000000000 : ℝ) (501950729937/1000000000000 : ℝ) (100390145989/200000000000 : ℝ) (250978375549/500000000000 : ℝ) (250978375553/500000000000 : ℝ) (501956751061/1000000000000 : ℝ) (50195675107/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8439/65536 : ℝ))) 4 (250978375549/500000000000 : ℝ) (250978375553/500000000000 : ℝ) (501956751061/1000000000000 : ℝ) (50195675107/100000000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8439/65536 : ℝ))) 5 (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8439/65536 : ℝ))) 6 (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8439/65536 : ℝ))) 7 (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8439/65536 : ℝ)) hmem 8 (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8439/65536 : ℝ))) hcmem 8 (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8439/65536 : ℝ)) (992000304383/1000000000000 : ℝ) (496000152193/500000000000 : ℝ) (501956751079/1000000000000 : ℝ) (31372296943/62500000000 : ℝ) (397415110317/500000000000 : ℝ) (198707555163/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1323_exp_lower
  have heNumeric : (1027452118301/500000000000 : ℝ)/4 ≤ Real.exp (-42628167324853/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452118301/500000000000 : ℝ)/4 ≤ Real.exp ((33755/262144 : ℝ)-(198707555163/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33755/262144 : ℝ) (8439/65536 : ℝ) (198707555163/250000000000 : ℝ) (1027452118301/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1324; no trusted numerical premise.
theorem cover8_leaf1324_exp_radius : (997989948870250407/1000000000000000000 : ℝ) ≤ Real.exp ((-33757/2097152 : ℝ)/8) ∧ Real.exp ((-33757/2097152 : ℝ)/8) ≤ (124748743608781301/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33757/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1324_exp_lower : (230028400408743017/250000000000000000 : ℝ) ≤ Real.exp ((-10657041475081/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657041475081/16000000000000 : ℝ)/8) ≤ (920113601634972069/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657041475081/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1324_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054904282341/1000000000000 : ℝ) ≤ 4*Real.exp (8439/65536 : ℝ)*Real.exp (-mu (radius 8 (33757/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054904282341/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33757/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1324_exp_radius
  have hrNumeric : (984032265869/1000000000000 : ℝ) ≤ Real.exp (-33757/2097152 : ℝ) ∧ Real.exp (-33757/2097152 : ℝ) ≤ (98403226587/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984032265869/1000000000000 : ℝ) ≤ (radius 8 (33757/262144 : ℝ)) ∧ (radius 8 (33757/262144 : ℝ)) ≤ (98403226587/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33757/262144 : ℝ)) (984032265869/1000000000000 : ℝ) (98403226587/100000000000 : ℝ) (71196067/400000000 : ℝ) (88995083753/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33757/262144 : ℝ)) (984032265869/1000000000000 : ℝ) (98403226587/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33757/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984032265869/1000000000000 : ℝ) (98403226587/100000000000 : ℝ) (496008066467/500000000000 : ℝ) (198403226587/200000000000 : ℝ) (198396800969/200000000000 : ℝ) (495992002423/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33757/262144 : ℝ)) 1 (496008066467/500000000000 : ℝ) (198403226587/200000000000 : ℝ) (198396800969/200000000000 : ℝ) (495992002423/500000000000 : ℝ) (992000068889/1000000000000 : ℝ) (992000068891/1000000000000 : ℝ) (992000068759/1000000000000 : ℝ) (992000068761/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33757/262144 : ℝ)) 2 (992000068889/1000000000000 : ℝ) (992000068891/1000000000000 : ℝ) (992000068759/1000000000000 : ℝ) (992000068761/1000000000000 : ℝ) (124000008603/125000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33757/262144 : ℝ)) 3 (124000008603/125000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33757/262144 : ℝ)) 4 (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33757/262144 : ℝ)) 5 (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33757/262144 : ℝ)) 6 (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33757/262144 : ℝ)) 7 (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33757/262144 : ℝ))) (71196067/400000000 : ℝ) (88995083753/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33757/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (71196067/400000000 : ℝ) (88995083753/500000000000 : ℝ) (471196067/800000000 : ℝ) (588995083753/1000000000000 : ℝ) (421888809403/1000000000000 : ℝ) (421888809411/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33757/262144 : ℝ))) 1 (471196067/800000000 : ℝ) (588995083753/1000000000000 : ℝ) (421888809403/1000000000000 : ℝ) (421888809411/1000000000000 : ℝ) (31590121661/62500000000 : ℝ) (252720973291/500000000000 : ℝ) (498488148933/1000000000000 : ℝ) (24924407447/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33757/262144 : ℝ))) 2 (31590121661/62500000000 : ℝ) (252720973291/500000000000 : ℝ) (498488148933/1000000000000 : ℝ) (24924407447/50000000000 : ℝ) (250982523877/500000000000 : ℝ) (501965047761/1000000000000 : ℝ) (125488251527/250000000000 : ℝ) (125488251529/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33757/262144 : ℝ))) 3 (250982523877/500000000000 : ℝ) (501965047761/1000000000000 : ℝ) (125488251527/250000000000 : ℝ) (125488251529/250000000000 : ℝ) (501959026931/1000000000000 : ℝ) (501959026939/1000000000000 : ℝ) (250979513447/500000000000 : ℝ) (501959026903/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33757/262144 : ℝ))) 4 (501959026931/1000000000000 : ℝ) (501959026939/1000000000000 : ℝ) (250979513447/500000000000 : ℝ) (501959026903/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33757/262144 : ℝ))) 5 (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33757/262144 : ℝ))) 6 (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33757/262144 : ℝ))) 7 (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33757/262144 : ℝ)) hmem 8 (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33757/262144 : ℝ))) hcmem 8 (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33757/262144 : ℝ)) (992000068823/1000000000000 : ℝ) (496000034413/500000000000 : ℝ) (15686219591/31250000000 : ℝ) (501959026921/1000000000000 : ℝ) (397417006537/500000000000 : ℝ) (794834013091/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1324_exp_lower
  have heNumeric : (2054904282341/1000000000000 : ℝ)/4 ≤ Real.exp (-10657041475081/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054904282341/1000000000000 : ℝ)/4 ≤ Real.exp ((8439/65536 : ℝ)-(794834013091/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8439/65536 : ℝ) (33757/262144 : ℝ) (794834013091/1000000000000 : ℝ) (2054904282341/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1300_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1300_certificate
#check SmaleRate.Proofs.cover8_leaf1301_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1301_certificate
#check SmaleRate.Proofs.cover8_leaf1302_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1302_certificate
#check SmaleRate.Proofs.cover8_leaf1303_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1303_certificate
#check SmaleRate.Proofs.cover8_leaf1304_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1304_certificate
#check SmaleRate.Proofs.cover8_leaf1305_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1305_certificate
#check SmaleRate.Proofs.cover8_leaf1306_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1306_certificate
#check SmaleRate.Proofs.cover8_leaf1307_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1307_certificate
#check SmaleRate.Proofs.cover8_leaf1308_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1308_certificate
#check SmaleRate.Proofs.cover8_leaf1309_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1309_certificate
#check SmaleRate.Proofs.cover8_leaf1310_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1310_certificate
#check SmaleRate.Proofs.cover8_leaf1311_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1311_certificate
#check SmaleRate.Proofs.cover8_leaf1312_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1312_certificate
#check SmaleRate.Proofs.cover8_leaf1313_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1313_certificate
#check SmaleRate.Proofs.cover8_leaf1314_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1314_certificate
#check SmaleRate.Proofs.cover8_leaf1315_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1315_certificate
#check SmaleRate.Proofs.cover8_leaf1316_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1316_certificate
#check SmaleRate.Proofs.cover8_leaf1317_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1317_certificate
#check SmaleRate.Proofs.cover8_leaf1318_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1318_certificate
#check SmaleRate.Proofs.cover8_leaf1319_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1319_certificate
#check SmaleRate.Proofs.cover8_leaf1320_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1320_certificate
#check SmaleRate.Proofs.cover8_leaf1321_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1321_certificate
#check SmaleRate.Proofs.cover8_leaf1322_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1322_certificate
#check SmaleRate.Proofs.cover8_leaf1323_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1323_certificate
#check SmaleRate.Proofs.cover8_leaf1324_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1324_certificate
