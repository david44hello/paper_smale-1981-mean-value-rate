/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0675; no trusted numerical premise.
theorem cover8_leaf0675_exp_radius : (998012731822638699/1000000000000000000 : ℝ) ≤ Real.exp ((-16687/1048576 : ℝ)/8) ∧ Real.exp ((-16687/1048576 : ℝ)/8) ≤ (9980127318226387/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16687/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0675_exp_lower : (184022697142937123/200000000000000000 : ℝ) ≤ Real.exp ((-17051292161809/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051292161809/25600000000000 : ℝ)/8) ≤ (57507092857167851/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051292161809/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0675_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902211249/1000000000000 : ℝ) ≤ 4*Real.exp (66747/524288 : ℝ)*Real.exp (-mu (radius 8 (16687/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902211249/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16687/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0675_exp_radius
  have hrNumeric : (984211994747/1000000000000 : ℝ) ≤ Real.exp (-16687/1048576 : ℝ) ∧ Real.exp (-16687/1048576 : ℝ) ≤ (246052998687/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984211994747/1000000000000 : ℝ) ≤ (radius 8 (16687/131072 : ℝ)) ∧ (radius 8 (16687/131072 : ℝ)) ≤ (246052998687/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16687/131072 : ℝ)) (984211994747/1000000000000 : ℝ) (246052998687/250000000000 : ℝ) (88496821121/500000000000 : ℝ) (22124205281/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16687/131072 : ℝ)) (984211994747/1000000000000 : ℝ) (246052998687/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16687/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984211994747/1000000000000 : ℝ) (246052998687/250000000000 : ℝ) (992105997373/1000000000000 : ℝ) (496052998687/500000000000 : ℝ) (496037295661/500000000000 : ℝ) (992074591323/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16687/131072 : ℝ)) 1 (992105997373/1000000000000 : ℝ) (496052998687/500000000000 : ℝ) (496037295661/500000000000 : ℝ) (992074591323/1000000000000 : ℝ) (992090294347/1000000000000 : ℝ) (992090294349/1000000000000 : ℝ) (992090294223/1000000000000 : ℝ) (39683611769/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16687/131072 : ℝ)) 2 (992090294347/1000000000000 : ℝ) (992090294349/1000000000000 : ℝ) (992090294223/1000000000000 : ℝ) (39683611769/40000000000 : ℝ) (198418058857/200000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16687/131072 : ℝ)) 3 (198418058857/200000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16687/131072 : ℝ)) 4 (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16687/131072 : ℝ)) 5 (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16687/131072 : ℝ)) 6 (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16687/131072 : ℝ)) 7 (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16687/131072 : ℝ))) (88496821121/500000000000 : ℝ) (22124205281/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16687/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88496821121/500000000000 : ℝ) (22124205281/125000000000 : ℝ) (588496821121/1000000000000 : ℝ) (147124205281/250000000000 : ℝ) (420706123371/1000000000000 : ℝ) (420706123379/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16687/131072 : ℝ))) 1 (588496821121/1000000000000 : ℝ) (147124205281/250000000000 : ℝ) (420706123371/1000000000000 : ℝ) (420706123379/1000000000000 : ℝ) (252300736123/500000000000 : ℝ) (126150368063/250000000000 : ℝ) (9951567037/20000000000 : ℝ) (497578351857/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16687/131072 : ℝ))) 2 (252300736123/500000000000 : ℝ) (126150368063/250000000000 : ℝ) (9951567037/20000000000 : ℝ) (497578351857/1000000000000 : ℝ) (31318119503/62500000000 : ℝ) (100217982411/200000000000 : ℝ) (250538803831/500000000000 : ℝ) (50107760767/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16687/131072 : ℝ))) 3 (31318119503/62500000000 : ℝ) (100217982411/200000000000 : ℝ) (250538803831/500000000000 : ℝ) (50107760767/100000000000 : ℝ) (100216751971/200000000000 : ℝ) (501083759863/1000000000000 : ℝ) (501083759817/1000000000000 : ℝ) (20043350393/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16687/131072 : ℝ))) 4 (100216751971/200000000000 : ℝ) (501083759863/1000000000000 : ℝ) (501083759817/1000000000000 : ℝ) (20043350393/40000000000 : ℝ) (125270939959/250000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16687/131072 : ℝ))) 5 (125270939959/250000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16687/131072 : ℝ))) 6 (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16687/131072 : ℝ))) 7 (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16687/131072 : ℝ)) hmem 8 (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16687/131072 : ℝ))) hcmem 8 (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16687/131072 : ℝ)) (248022573571/250000000000 : ℝ) (992090294287/1000000000000 : ℝ) (100216751967/200000000000 : ℝ) (125270939961/250000000000 : ℝ) (49585993703/62500000000 : ℝ) (158675179853/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0675_exp_lower
  have heNumeric : (2054902211249/1000000000000 : ℝ)/4 ≤ Real.exp (-17051292161809/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902211249/1000000000000 : ℝ)/4 ≤ Real.exp ((66747/524288 : ℝ)-(158675179853/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66747/524288 : ℝ) (16687/131072 : ℝ) (158675179853/200000000000 : ℝ) (2054902211249/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0676; no trusted numerical premise.
theorem cover8_leaf0676_exp_radius : (998012702079541961/1000000000000000000 : ℝ) ≤ Real.exp ((-66749/4194304 : ℝ)/8) ∧ Real.exp ((-66749/4194304 : ℝ)/8) ≤ (499006351039770981/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66749/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0676_exp_lower : (920113485302892599/1000000000000000000 : ℝ) ≤ Real.exp ((-21314115316833/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314115316833/32000000000000 : ℝ)/8) ≤ (4600567426514463/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314115316833/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0676_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725550973/250000000000 : ℝ) ≤ 4*Real.exp (16687/131072 : ℝ)*Real.exp (-mu (radius 8 (66749/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725550973/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66749/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0676_exp_radius
  have hrNumeric : (246052940023/250000000000 : ℝ) ≤ Real.exp (-66749/4194304 : ℝ) ∧ Real.exp (-66749/4194304 : ℝ) ≤ (984211760093/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246052940023/250000000000 : ℝ) ≤ (radius 8 (66749/524288 : ℝ)) ∧ (radius 8 (66749/524288 : ℝ)) ≤ (984211760093/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66749/524288 : ℝ)) (246052940023/250000000000 : ℝ) (984211760093/1000000000000 : ℝ) (176994947087/1000000000000 : ℝ) (88497473547/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66749/524288 : ℝ)) (246052940023/250000000000 : ℝ) (984211760093/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66749/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246052940023/250000000000 : ℝ) (984211760093/1000000000000 : ℝ) (496052940023/500000000000 : ℝ) (992105880047/1000000000000 : ℝ) (992074473057/1000000000000 : ℝ) (496037236529/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66749/524288 : ℝ)) 1 (496052940023/500000000000 : ℝ) (992105880047/1000000000000 : ℝ) (992074473057/1000000000000 : ℝ) (496037236529/500000000000 : ℝ) (992090176551/1000000000000 : ℝ) (992090176553/1000000000000 : ℝ) (992090176427/1000000000000 : ℝ) (992090176429/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66749/524288 : ℝ)) 2 (992090176551/1000000000000 : ℝ) (992090176553/1000000000000 : ℝ) (992090176427/1000000000000 : ℝ) (992090176429/1000000000000 : ℝ) (992090176489/1000000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66749/524288 : ℝ)) 3 (992090176489/1000000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66749/524288 : ℝ)) 4 (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66749/524288 : ℝ)) 5 (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66749/524288 : ℝ)) 6 (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66749/524288 : ℝ)) 7 (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66749/524288 : ℝ))) (176994947087/1000000000000 : ℝ) (88497473547/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66749/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176994947087/1000000000000 : ℝ) (88497473547/500000000000 : ℝ) (588497473543/1000000000000 : ℝ) (588497473547/1000000000000 : ℝ) (420707674147/1000000000000 : ℝ) (420707674157/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66749/524288 : ℝ))) 1 (588497473543/1000000000000 : ℝ) (588497473547/1000000000000 : ℝ) (420707674147/1000000000000 : ℝ) (420707674157/1000000000000 : ℝ) (100920514769/200000000000 : ℝ) (126150643463/250000000000 : ℝ) (497579544731/1000000000000 : ℝ) (24878977237/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66749/524288 : ℝ))) 2 (100920514769/200000000000 : ℝ) (126150643463/250000000000 : ℝ) (497579544731/1000000000000 : ℝ) (24878977237/50000000000 : ℝ) (62636382411/125000000000 : ℝ) (15659095603/31250000000 : ℝ) (2004315021/4000000000 : ℝ) (25053937763/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66749/524288 : ℝ))) 3 (62636382411/125000000000 : ℝ) (15659095603/31250000000 : ℝ) (2004315021/4000000000 : ℝ) (25053937763/50000000000 : ℝ) (501084907269/1000000000000 : ℝ) (250542453639/500000000000 : ℝ) (501084907231/1000000000000 : ℝ) (501084907241/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66749/524288 : ℝ))) 4 (501084907269/1000000000000 : ℝ) (250542453639/500000000000 : ℝ) (501084907231/1000000000000 : ℝ) (501084907241/1000000000000 : ℝ) (2004339629/4000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66749/524288 : ℝ))) 5 (2004339629/4000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66749/524288 : ℝ))) 6 (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66749/524288 : ℝ))) 7 (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66749/524288 : ℝ)) hmem 8 (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66749/524288 : ℝ))) hcmem 8 (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66749/524288 : ℝ)) (124011272061/125000000000 : ℝ) (992090176491/1000000000000 : ℝ) (501084907249/1000000000000 : ℝ) (25054245363/50000000000 : ℝ) (793377810173/1000000000000 : ℝ) (396688905097/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0676_exp_lower
  have heNumeric : (513725550973/250000000000 : ℝ)/4 ≤ Real.exp (-21314115316833/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725550973/250000000000 : ℝ)/4 ≤ Real.exp ((16687/131072 : ℝ)-(396688905097/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16687/131072 : ℝ) (66749/524288 : ℝ) (396688905097/500000000000 : ℝ) (513725550973/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0677; no trusted numerical premise.
theorem cover8_leaf0677_exp_radius : (99801267233644611/100000000000000000 : ℝ) ≤ Real.exp ((-33375/2097152 : ℝ)/8) ∧ Real.exp ((-33375/2097152 : ℝ)/8) ≤ (998012672336446111/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33375/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0677_exp_lower : (115014185611818751/125000000000000000 : ℝ) ≤ Real.exp ((-85256461721779/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256461721779/128000000000000 : ℝ)/8) ≤ (920113484894550009/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256461721779/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0677_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725549149/250000000000 : ℝ) ≤ 4*Real.exp (66749/524288 : ℝ)*Real.exp (-mu (radius 8 (33375/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725549149/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33375/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0677_exp_radius
  have hrNumeric : (492105762719/500000000000 : ℝ) ≤ Real.exp (-33375/2097152 : ℝ) ∧ Real.exp (-33375/2097152 : ℝ) ≤ (984211525439/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492105762719/500000000000 : ℝ) ≤ (radius 8 (33375/262144 : ℝ)) ∧ (radius 8 (33375/262144 : ℝ)) ≤ (984211525439/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33375/262144 : ℝ)) (492105762719/500000000000 : ℝ) (984211525439/1000000000000 : ℝ) (88498125959/500000000000 : ℝ) (44249062981/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33375/262144 : ℝ)) (492105762719/500000000000 : ℝ) (984211525439/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33375/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492105762719/500000000000 : ℝ) (984211525439/1000000000000 : ℝ) (992105762719/1000000000000 : ℝ) (6200661017/6250000000 : ℝ) (992074354793/1000000000000 : ℝ) (496037177397/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33375/262144 : ℝ)) 1 (992105762719/1000000000000 : ℝ) (6200661017/6250000000 : ℝ) (992074354793/1000000000000 : ℝ) (496037177397/500000000000 : ℝ) (248022514689/250000000000 : ℝ) (992090058757/1000000000000 : ℝ) (992090058631/1000000000000 : ℝ) (992090058633/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33375/262144 : ℝ)) 2 (248022514689/250000000000 : ℝ) (992090058757/1000000000000 : ℝ) (992090058631/1000000000000 : ℝ) (992090058633/1000000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33375/262144 : ℝ)) 3 (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33375/262144 : ℝ)) 4 (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33375/262144 : ℝ)) 5 (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33375/262144 : ℝ)) 6 (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33375/262144 : ℝ)) 7 (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33375/262144 : ℝ))) (88498125959/500000000000 : ℝ) (44249062981/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33375/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88498125959/500000000000 : ℝ) (44249062981/250000000000 : ℝ) (588498125959/1000000000000 : ℝ) (294249062981/500000000000 : ℝ) (210354612451/500000000000 : ℝ) (42070922491/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33375/262144 : ℝ))) 1 (588498125959/1000000000000 : ℝ) (294249062981/500000000000 : ℝ) (210354612451/500000000000 : ℝ) (42070922491/100000000000 : ℝ) (50460367543/100000000000 : ℝ) (126150918859/250000000000 : ℝ) (497580737597/1000000000000 : ℝ) (124395184401/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33375/262144 : ℝ))) 2 (50460367543/100000000000 : ℝ) (126150918859/250000000000 : ℝ) (497580737597/1000000000000 : ℝ) (124395184401/250000000000 : ℝ) (501092206513/1000000000000 : ℝ) (12527305163/25000000000 : ℝ) (62634987853/125000000000 : ℝ) (31317493927/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33375/262144 : ℝ))) 3 (501092206513/1000000000000 : ℝ) (12527305163/25000000000 : ℝ) (62634987853/125000000000 : ℝ) (31317493927/62500000000 : ℝ) (125271513667/250000000000 : ℝ) (125271513669/250000000000 : ℝ) (50108605463/100000000000 : ℝ) (501086054639/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33375/262144 : ℝ))) 4 (125271513667/250000000000 : ℝ) (125271513669/250000000000 : ℝ) (50108605463/100000000000 : ℝ) (501086054639/1000000000000 : ℝ) (501086054649/1000000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33375/262144 : ℝ))) 5 (501086054649/1000000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33375/262144 : ℝ))) 6 (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33375/262144 : ℝ))) 7 (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33375/262144 : ℝ)) hmem 8 (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33375/262144 : ℝ))) hcmem 8 (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33375/262144 : ℝ)) (992090058693/1000000000000 : ℝ) (198418011739/200000000000 : ℝ) (62635756831/125000000000 : ℝ) (250543027329/500000000000 : ℝ) (31735188843/40000000000 : ℝ) (793379721093/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0677_exp_lower
  have heNumeric : (513725549149/250000000000 : ℝ)/4 ≤ Real.exp (-85256461721779/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725549149/250000000000 : ℝ)/4 ≤ Real.exp ((66749/524288 : ℝ)-(793379721093/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66749/524288 : ℝ) (33375/262144 : ℝ) (793379721093/1000000000000 : ℝ) (513725549149/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0678; no trusted numerical premise.
theorem cover8_leaf0678_exp_radius : (499006321296675573/500000000000000000 : ℝ) ≤ Real.exp ((-66751/4194304 : ℝ)/8) ∧ Real.exp ((-66751/4194304 : ℝ)/8) ≤ (998012642593351147/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66751/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0678_exp_lower : (920113484488162659/1000000000000000000 : ℝ) ≤ Real.exp ((-1705129243481/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705129243481/2560000000000 : ℝ)/8) ≤ (46005674224408133/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705129243481/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0678_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980437867/200000000000 : ℝ) ≤ 4*Real.exp (33375/262144 : ℝ)*Real.exp (-mu (radius 8 (66751/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (410980437867/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66751/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0678_exp_radius
  have hrNumeric : (30756602837/31250000000 : ℝ) ≤ Real.exp (-66751/4194304 : ℝ) ∧ Real.exp (-66751/4194304 : ℝ) ≤ (196842258157/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30756602837/31250000000 : ℝ) ≤ (radius 8 (66751/524288 : ℝ)) ∧ (radius 8 (66751/524288 : ℝ)) ≤ (196842258157/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66751/524288 : ℝ)) (30756602837/31250000000 : ℝ) (196842258157/200000000000 : ℝ) (88498778369/500000000000 : ℝ) (22124694593/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66751/524288 : ℝ)) (30756602837/31250000000 : ℝ) (196842258157/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66751/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30756602837/31250000000 : ℝ) (196842258157/200000000000 : ℝ) (62006602837/62500000000 : ℝ) (992105645393/1000000000000 : ℝ) (62004639783/62500000000 : ℝ) (99207423653/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66751/524288 : ℝ)) 1 (62006602837/62500000000 : ℝ) (992105645393/1000000000000 : ℝ) (62004639783/62500000000 : ℝ) (99207423653/100000000000 : ℝ) (6200562131/6250000000 : ℝ) (496044970481/500000000000 : ℝ) (198417988167/200000000000 : ℝ) (496044970419/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66751/524288 : ℝ)) 2 (6200562131/6250000000 : ℝ) (496044970481/500000000000 : ℝ) (198417988167/200000000000 : ℝ) (496044970419/500000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66751/524288 : ℝ)) 3 (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66751/524288 : ℝ)) 4 (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66751/524288 : ℝ)) 5 (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66751/524288 : ℝ)) 6 (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66751/524288 : ℝ)) 7 (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66751/524288 : ℝ))) (88498778369/500000000000 : ℝ) (22124694593/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66751/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88498778369/500000000000 : ℝ) (22124694593/125000000000 : ℝ) (588498778369/1000000000000 : ℝ) (147124694593/250000000000 : ℝ) (210355387819/500000000000 : ℝ) (210355387823/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66751/524288 : ℝ))) 1 (588498778369/1000000000000 : ℝ) (147124694593/250000000000 : ℝ) (210355387819/500000000000 : ℝ) (210355387823/500000000000 : ℝ) (504604777003/1000000000000 : ℝ) (504604777009/1000000000000 : ℝ) (497581930449/1000000000000 : ℝ) (62197741307/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66751/524288 : ℝ))) 2 (504604777003/1000000000000 : ℝ) (504604777009/1000000000000 : ℝ) (497581930449/1000000000000 : ℝ) (62197741307/125000000000 : ℝ) (250546676863/500000000000 : ℝ) (501093353733/1000000000000 : ℝ) (100216210077/200000000000 : ℝ) (62635131299/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66751/524288 : ℝ))) 3 (250546676863/500000000000 : ℝ) (501093353733/1000000000000 : ℝ) (100216210077/200000000000 : ℝ) (62635131299/125000000000 : ℝ) (100217440411/200000000000 : ℝ) (501087202063/1000000000000 : ℝ) (501087202017/1000000000000 : ℝ) (20043488081/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66751/524288 : ℝ))) 4 (100217440411/200000000000 : ℝ) (501087202063/1000000000000 : ℝ) (501087202017/1000000000000 : ℝ) (20043488081/40000000000 : ℝ) (125271800509/250000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66751/524288 : ℝ))) 5 (125271800509/250000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66751/524288 : ℝ))) 6 (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66751/524288 : ℝ))) 7 (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66751/524288 : ℝ)) hmem 8 (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66751/524288 : ℝ))) hcmem 8 (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66751/524288 : ℝ)) (992089940897/1000000000000 : ℝ) (9920899409/10000000000 : ℝ) (100217440407/200000000000 : ℝ) (125271800511/250000000000 : ℝ) (396690815979/500000000000 : ℝ) (31735265279/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0678_exp_lower
  have heNumeric : (410980437867/200000000000 : ℝ)/4 ≤ Real.exp (-1705129243481/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980437867/200000000000 : ℝ)/4 ≤ Real.exp ((33375/262144 : ℝ)-(31735265279/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33375/262144 : ℝ) (66751/524288 : ℝ) (31735265279/40000000000 : ℝ) (410980437867/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0679; no trusted numerical premise.
theorem cover8_leaf0679_exp_radius : (998012612850257067/1000000000000000000 : ℝ) ≤ Real.exp ((-1043/65536 : ℝ)/8) ∧ Real.exp ((-1043/65536 : ℝ)/8) ≤ (249503153212564267/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1043/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0679_exp_lower : (920113484082925451/1000000000000000000 : ℝ) ≤ Real.exp ((-85256462625041/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256462625041/128000000000000 : ℝ)/8) ≤ (230028371020731363/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256462625041/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0679_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980436419/200000000000 : ℝ) ≤ 4*Real.exp (66751/524288 : ℝ)*Real.exp (-mu (radius 8 (1043/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (410980436419/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1043/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0679_exp_radius
  have hrNumeric : (984211056129/1000000000000 : ℝ) ≤ Real.exp (-1043/65536 : ℝ) ∧ Real.exp (-1043/65536 : ℝ) ≤ (98421105613/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984211056129/1000000000000 : ℝ) ≤ (radius 8 (1043/8192 : ℝ)) ∧ (radius 8 (1043/8192 : ℝ)) ≤ (98421105613/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1043/8192 : ℝ)) (984211056129/1000000000000 : ℝ) (98421105613/100000000000 : ℝ) (88499430777/500000000000 : ℝ) (4424971539/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1043/8192 : ℝ)) (984211056129/1000000000000 : ℝ) (98421105613/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1043/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984211056129/1000000000000 : ℝ) (98421105613/100000000000 : ℝ) (3875412219/3906250000 : ℝ) (198421105613/200000000000 : ℝ) (992074118263/1000000000000 : ℝ) (198414823653/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1043/8192 : ℝ)) 1 (3875412219/3906250000 : ℝ) (198421105613/200000000000 : ℝ) (992074118263/1000000000000 : ℝ) (198414823653/200000000000 : ℝ) (992089823163/1000000000000 : ℝ) (198417964633/200000000000 : ℝ) (992089823039/1000000000000 : ℝ) (992089823041/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1043/8192 : ℝ)) 2 (992089823163/1000000000000 : ℝ) (198417964633/200000000000 : ℝ) (992089823039/1000000000000 : ℝ) (992089823041/1000000000000 : ℝ) (992089823101/1000000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1043/8192 : ℝ)) 3 (992089823101/1000000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1043/8192 : ℝ)) 4 (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1043/8192 : ℝ)) 5 (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1043/8192 : ℝ)) 6 (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1043/8192 : ℝ)) 7 (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1043/8192 : ℝ))) (88499430777/500000000000 : ℝ) (4424971539/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1043/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88499430777/500000000000 : ℝ) (4424971539/25000000000 : ℝ) (588499430777/1000000000000 : ℝ) (29424971539/50000000000 : ℝ) (420712326363/1000000000000 : ℝ) (420712326371/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1043/8192 : ℝ))) 1 (588499430777/1000000000000 : ℝ) (29424971539/50000000000 : ℝ) (420712326363/1000000000000 : ℝ) (420712326371/1000000000000 : ℝ) (50460587857/100000000000 : ℝ) (31537867411/62500000000 : ℝ) (124395780823/250000000000 : ℝ) (497583123299/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1043/8192 : ℝ))) 2 (50460587857/100000000000 : ℝ) (31537867411/62500000000 : ℝ) (124395780823/250000000000 : ℝ) (497583123299/1000000000000 : ℝ) (501094500931/1000000000000 : ℝ) (250547250469/500000000000 : ℝ) (501082197937/1000000000000 : ℝ) (100216439589/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1043/8192 : ℝ))) 3 (501094500931/1000000000000 : ℝ) (250547250469/500000000000 : ℝ) (501082197937/1000000000000 : ℝ) (100216439589/200000000000 : ℝ) (250544174717/500000000000 : ℝ) (250544174721/500000000000 : ℝ) (125272087349/250000000000 : ℝ) (125272087351/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1043/8192 : ℝ))) 4 (250544174717/500000000000 : ℝ) (250544174721/500000000000 : ℝ) (125272087349/250000000000 : ℝ) (125272087351/250000000000 : ℝ) (100217669883/200000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1043/8192 : ℝ))) 5 (100217669883/200000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1043/8192 : ℝ))) 6 (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1043/8192 : ℝ))) 7 (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1043/8192 : ℝ)) hmem 8 (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1043/8192 : ℝ))) hcmem 8 (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1043/8192 : ℝ)) (9920898231/10000000000 : ℝ) (992089823103/1000000000000 : ℝ) (250544174707/500000000000 : ℝ) (501088349423/1000000000000 : ℝ) (79338354283/100000000000 : ℝ) (793383542847/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0679_exp_lower
  have heNumeric : (410980436419/200000000000 : ℝ)/4 ≤ Real.exp (-85256462625041/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980436419/200000000000 : ℝ)/4 ≤ Real.exp ((66751/524288 : ℝ)-(793383542847/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66751/524288 : ℝ) (1043/8192 : ℝ) (793383542847/1000000000000 : ℝ) (410980436419/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0680; no trusted numerical premise.
theorem cover8_leaf0680_exp_radius : (7984100664857311/8000000000000000 : ℝ) ≤ Real.exp ((-66753/4194304 : ℝ)/8) ∧ Real.exp ((-66753/4194304 : ℝ)/8) ≤ (249503145776790969/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66753/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0680_exp_lower : (920113483680908641/1000000000000000000 : ℝ) ≤ Real.exp ((-1332132235507/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332132235507/2000000000000 : ℝ)/8) ≤ (460056741840454321/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332132235507/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0680_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (32107846483/15625000000 : ℝ) ≤ 4*Real.exp (1043/8192 : ℝ)*Real.exp (-mu (radius 8 (66753/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (32107846483/15625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66753/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0680_exp_radius
  have hrNumeric : (39368432859/40000000000 : ℝ) ≤ Real.exp (-66753/4194304 : ℝ) ∧ Real.exp (-66753/4194304 : ℝ) ≤ (246052705369/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39368432859/40000000000 : ℝ) ≤ (radius 8 (66753/524288 : ℝ)) ∧ (radius 8 (66753/524288 : ℝ)) ≤ (246052705369/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66753/524288 : ℝ)) (39368432859/40000000000 : ℝ) (246052705369/250000000000 : ℝ) (88500083177/500000000000 : ℝ) (177000166361/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66753/524288 : ℝ)) (39368432859/40000000000 : ℝ) (246052705369/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66753/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39368432859/40000000000 : ℝ) (246052705369/250000000000 : ℝ) (992105410737/1000000000000 : ℝ) (496052705369/500000000000 : ℝ) (992073999999/1000000000000 : ℝ) (496037/500000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66753/524288 : ℝ)) 1 (992105410737/1000000000000 : ℝ) (496052705369/500000000000 : ℝ) (992073999999/1000000000000 : ℝ) (496037/500000 : ℝ) (124011213171/125000000000 : ℝ) (992089705369/1000000000000 : ℝ) (992089705243/1000000000000 : ℝ) (198417941049/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66753/524288 : ℝ)) 2 (124011213171/125000000000 : ℝ) (992089705369/1000000000000 : ℝ) (992089705243/1000000000000 : ℝ) (198417941049/200000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66753/524288 : ℝ)) 3 (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66753/524288 : ℝ)) 4 (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66753/524288 : ℝ)) 5 (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66753/524288 : ℝ)) 6 (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66753/524288 : ℝ)) 7 (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66753/524288 : ℝ))) (88500083177/500000000000 : ℝ) (177000166361/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66753/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88500083177/500000000000 : ℝ) (177000166361/1000000000000 : ℝ) (588500083177/1000000000000 : ℝ) (588500083181/1000000000000 : ℝ) (420713877063/1000000000000 : ℝ) (420713877073/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66753/524288 : ℝ))) 1 (588500083177/1000000000000 : ℝ) (588500083181/1000000000000 : ℝ) (420713877063/1000000000000 : ℝ) (420713877073/1000000000000 : ℝ) (12615174503/25000000000 : ℝ) (504606980127/1000000000000 : ℝ) (124396079029/250000000000 : ℝ) (3980674529/8000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66753/524288 : ℝ))) 2 (12615174503/25000000000 : ℝ) (504606980127/1000000000000 : ℝ) (124396079029/250000000000 : ℝ) (3980674529/8000000000 : ℝ) (250547824059/500000000000 : ℝ) (250547824063/500000000000 : ℝ) (7829427273/15625000000 : ℝ) (501083345481/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66753/524288 : ℝ))) 3 (250547824059/500000000000 : ℝ) (250547824063/500000000000 : ℝ) (7829427273/15625000000 : ℝ) (501083345481/1000000000000 : ℝ) (100217899359/200000000000 : ℝ) (125272374201/250000000000 : ℝ) (501089496757/1000000000000 : ℝ) (250544748383/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66753/524288 : ℝ))) 4 (100217899359/200000000000 : ℝ) (125272374201/250000000000 : ℝ) (501089496757/1000000000000 : ℝ) (250544748383/500000000000 : ℝ) (62636187097/125000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66753/524288 : ℝ))) 5 (62636187097/125000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66753/524288 : ℝ))) 6 (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66753/524288 : ℝ))) 7 (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66753/524288 : ℝ)) hmem 8 (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66753/524288 : ℝ))) hcmem 8 (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66753/524288 : ℝ)) (198417941061/200000000000 : ℝ) (992089705307/1000000000000 : ℝ) (20043579871/40000000000 : ℝ) (100217899357/200000000000 : ℝ) (793385453673/1000000000000 : ℝ) (793385453691/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0680_exp_lower
  have heNumeric : (32107846483/15625000000 : ℝ)/4 ≤ Real.exp (-1332132235507/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (32107846483/15625000000 : ℝ)/4 ≤ Real.exp ((1043/8192 : ℝ)-(793385453691/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1043/8192 : ℝ) (66753/524288 : ℝ) (793385453691/1000000000000 : ℝ) (32107846483/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0681; no trusted numerical premise.
theorem cover8_leaf0681_exp_radius : (99801255336407157/100000000000000000 : ℝ) ≤ Real.exp ((-33377/2097152 : ℝ)/8) ∧ Real.exp ((-33377/2097152 : ℝ)/8) ≤ (998012553364071571/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33377/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0681_exp_lower : (920113483281077101/1000000000000000000 : ℝ) ≤ Real.exp ((-85256463517423/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256463517423/128000000000000 : ℝ)/8) ≤ (460056741640538551/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256463517423/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0681_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902167769/1000000000000 : ℝ) ≤ 4*Real.exp (66753/524288 : ℝ)*Real.exp (-mu (radius 8 (33377/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902167769/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33377/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0681_exp_radius
  have hrNumeric : (984210586821/1000000000000 : ℝ) ≤ Real.exp (-33377/2097152 : ℝ) ∧ Real.exp (-33377/2097152 : ℝ) ≤ (492105293411/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984210586821/1000000000000 : ℝ) ≤ (radius 8 (33377/262144 : ℝ)) ∧ (radius 8 (33377/262144 : ℝ)) ≤ (492105293411/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33377/262144 : ℝ)) (984210586821/1000000000000 : ℝ) (492105293411/500000000000 : ℝ) (35400294229/200000000000 : ℝ) (177001471151/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33377/262144 : ℝ)) (984210586821/1000000000000 : ℝ) (492105293411/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33377/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984210586821/1000000000000 : ℝ) (492105293411/500000000000 : ℝ) (99210529341/100000000000 : ℝ) (992105293411/1000000000000 : ℝ) (198414776347/200000000000 : ℝ) (124009235217/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33377/262144 : ℝ)) 1 (99210529341/100000000000 : ℝ) (992105293411/1000000000000 : ℝ) (198414776347/200000000000 : ℝ) (124009235217/125000000000 : ℝ) (248022396893/250000000000 : ℝ) (496044793787/500000000000 : ℝ) (124011198431/125000000000 : ℝ) (19841791749/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33377/262144 : ℝ)) 2 (248022396893/250000000000 : ℝ) (496044793787/500000000000 : ℝ) (124011198431/125000000000 : ℝ) (19841791749/20000000000 : ℝ) (99208958751/100000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33377/262144 : ℝ)) 3 (99208958751/100000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33377/262144 : ℝ)) 4 (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33377/262144 : ℝ)) 5 (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33377/262144 : ℝ)) 6 (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33377/262144 : ℝ)) 7 (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33377/262144 : ℝ))) (35400294229/200000000000 : ℝ) (177001471151/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33377/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35400294229/200000000000 : ℝ) (177001471151/1000000000000 : ℝ) (147125183893/250000000000 : ℝ) (73562591947/125000000000 : ℝ) (420715427747/1000000000000 : ℝ) (84143085551/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33377/262144 : ℝ))) 1 (147125183893/250000000000 : ℝ) (73562591947/125000000000 : ℝ) (420715427747/1000000000000 : ℝ) (84143085551/200000000000 : ℝ) (504608081659/1000000000000 : ℝ) (252304040833/500000000000 : ℝ) (7774773577/15625000000 : ℝ) (99517101787/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33377/262144 : ℝ))) 2 (504608081659/1000000000000 : ℝ) (252304040833/500000000000 : ℝ) (7774773577/15625000000 : ℝ) (99517101787/200000000000 : ℝ) (501096795293/1000000000000 : ℝ) (501096795301/1000000000000 : ℝ) (125271123249/250000000000 : ℝ) (125271123251/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33377/262144 : ℝ))) 3 (501096795293/1000000000000 : ℝ) (501096795301/1000000000000 : ℝ) (125271123249/250000000000 : ℝ) (125271123251/250000000000 : ℝ) (31318165259/62500000000 : ℝ) (501090644153/1000000000000 : ℝ) (250545322053/500000000000 : ℝ) (100218128823/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33377/262144 : ℝ))) 4 (31318165259/62500000000 : ℝ) (501090644153/1000000000000 : ℝ) (250545322053/500000000000 : ℝ) (100218128823/200000000000 : ℝ) (4008725153/8000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33377/262144 : ℝ))) 5 (4008725153/8000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33377/262144 : ℝ))) 6 (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33377/262144 : ℝ))) 7 (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33377/262144 : ℝ)) hmem 8 (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33377/262144 : ℝ))) hcmem 8 (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33377/262144 : ℝ)) (992089587509/1000000000000 : ℝ) (124011198439/125000000000 : ℝ) (125272661031/250000000000 : ℝ) (250545322067/500000000000 : ℝ) (793387364497/1000000000000 : ℝ) (198346841129/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0681_exp_lower
  have heNumeric : (2054902167769/1000000000000 : ℝ)/4 ≤ Real.exp (-85256463517423/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902167769/1000000000000 : ℝ)/4 ≤ Real.exp ((66753/524288 : ℝ)-(198346841129/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66753/524288 : ℝ) (33377/262144 : ℝ) (198346841129/250000000000 : ℝ) (2054902167769/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0682; no trusted numerical premise.
theorem cover8_leaf0682_exp_radius : (998012523620980151/1000000000000000000 : ℝ) ≤ Real.exp ((-66755/4194304 : ℝ)/8) ∧ Real.exp ((-66755/4194304 : ℝ)/8) ≤ (124751565452622519/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66755/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0682_exp_lower : (92011348288343083/100000000000000000 : ℝ) ≤ Real.exp ((-42628231979983/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628231979983/64000000000000 : ℝ)/8) ≤ (920113482883430831/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628231979983/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0682_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862770083/125000000000 : ℝ) ≤ 4*Real.exp (33377/262144 : ℝ)*Real.exp (-mu (radius 8 (66755/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862770083/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66755/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0682_exp_radius
  have hrNumeric : (984210352167/1000000000000 : ℝ) ≤ Real.exp (-66755/4194304 : ℝ) ∧ Real.exp (-66755/4194304 : ℝ) ≤ (123026294021/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984210352167/1000000000000 : ℝ) ≤ (radius 8 (66755/524288 : ℝ)) ∧ (radius 8 (66755/524288 : ℝ)) ≤ (123026294021/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66755/524288 : ℝ)) (984210352167/1000000000000 : ℝ) (123026294021/125000000000 : ℝ) (7080111037/40000000000 : ℝ) (44250693983/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66755/524288 : ℝ)) (984210352167/1000000000000 : ℝ) (123026294021/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66755/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984210352167/1000000000000 : ℝ) (123026294021/125000000000 : ℝ) (992105176083/1000000000000 : ℝ) (248026294021/250000000000 : ℝ) (99207376347/100000000000 : ℝ) (62004610217/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66755/524288 : ℝ)) 1 (992105176083/1000000000000 : ℝ) (248026294021/250000000000 : ℝ) (99207376347/100000000000 : ℝ) (62004610217/62500000000 : ℝ) (62005591861/62500000000 : ℝ) (496044734889/500000000000 : ℝ) (248022367413/250000000000 : ℝ) (496044734827/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66755/524288 : ℝ)) 2 (62005591861/62500000000 : ℝ) (496044734889/500000000000 : ℝ) (248022367413/250000000000 : ℝ) (496044734827/500000000000 : ℝ) (496044734857/500000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66755/524288 : ℝ)) 3 (496044734857/500000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66755/524288 : ℝ)) 4 (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66755/524288 : ℝ)) 5 (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66755/524288 : ℝ)) 6 (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66755/524288 : ℝ)) 7 (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66755/524288 : ℝ))) (7080111037/40000000000 : ℝ) (44250693983/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66755/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7080111037/40000000000 : ℝ) (44250693983/250000000000 : ℝ) (294250693981/500000000000 : ℝ) (294250693983/500000000000 : ℝ) (420716978413/1000000000000 : ℝ) (210358489211/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66755/524288 : ℝ))) 1 (294250693981/500000000000 : ℝ) (294250693983/500000000000 : ℝ) (420716978413/1000000000000 : ℝ) (210358489211/500000000000 : ℝ) (504609183187/1000000000000 : ℝ) (252304591597/500000000000 : ℝ) (248793350863/500000000000 : ℝ) (248793350867/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66755/524288 : ℝ))) 2 (504609183187/1000000000000 : ℝ) (252304591597/500000000000 : ℝ) (248793350863/500000000000 : ℝ) (248793350867/500000000000 : ℝ) (62637242807/125000000000 : ℝ) (7829655351/15625000000 : ℝ) (501085640507/1000000000000 : ℝ) (100217128103/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66755/524288 : ℝ))) 3 (62637242807/125000000000 : ℝ) (7829655351/15625000000 : ℝ) (501085640507/1000000000000 : ℝ) (100217128103/200000000000 : ℝ) (501091791481/1000000000000 : ℝ) (50109179149/100000000000 : ℝ) (501091791443/1000000000000 : ℝ) (125272947863/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66755/524288 : ℝ))) 4 (501091791481/1000000000000 : ℝ) (50109179149/100000000000 : ℝ) (501091791443/1000000000000 : ℝ) (125272947863/250000000000 : ℝ) (250545895731/500000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66755/524288 : ℝ))) 5 (250545895731/500000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66755/524288 : ℝ))) 6 (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66755/524288 : ℝ))) 7 (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66755/524288 : ℝ)) hmem 8 (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66755/524288 : ℝ))) hcmem 8 (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66755/524288 : ℝ)) (992089469713/1000000000000 : ℝ) (248022367429/250000000000 : ℝ) (501091791461/1000000000000 : ℝ) (501091791471/1000000000000 : ℝ) (793389275303/1000000000000 : ℝ) (396694637661/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0682_exp_lower
  have heNumeric : (256862770083/125000000000 : ℝ)/4 ≤ Real.exp (-42628231979983/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862770083/125000000000 : ℝ)/4 ≤ Real.exp ((33377/262144 : ℝ)-(396694637661/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33377/262144 : ℝ) (66755/524288 : ℝ) (396694637661/500000000000 : ℝ) (256862770083/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0683; no trusted numerical premise.
theorem cover8_leaf0683_exp_radius : (499006246938944809/500000000000000000 : ℝ) ≤ Real.exp ((-16689/1048576 : ℝ)/8) ∧ Real.exp ((-16689/1048576 : ℝ)/8) ≤ (998012493877889619/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16689/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0683_exp_lower : (920113482487969829/1000000000000000000 : ℝ) ≤ Real.exp ((-85256464400077/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256464400077/128000000000000 : ℝ)/8) ≤ (92011348248796983/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256464400077/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0683_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902153599/1000000000000 : ℝ) ≤ 4*Real.exp (66755/524288 : ℝ)*Real.exp (-mu (radius 8 (16689/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902153599/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16689/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0683_exp_radius
  have hrNumeric : (984210117513/1000000000000 : ℝ) ≤ Real.exp (-16689/1048576 : ℝ) ∧ Real.exp (-16689/1048576 : ℝ) ≤ (492105058757/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984210117513/1000000000000 : ℝ) ≤ (radius 8 (16689/131072 : ℝ)) ∧ (radius 8 (16689/131072 : ℝ)) ≤ (492105058757/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16689/131072 : ℝ)) (984210117513/1000000000000 : ℝ) (492105058757/500000000000 : ℝ) (22125510087/125000000000 : ℝ) (88502040351/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16689/131072 : ℝ)) (984210117513/1000000000000 : ℝ) (492105058757/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16689/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984210117513/1000000000000 : ℝ) (492105058757/500000000000 : ℝ) (248026264689/250000000000 : ℝ) (992105058757/1000000000000 : ℝ) (496036822603/500000000000 : ℝ) (992073645207/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16689/131072 : ℝ)) 1 (248026264689/250000000000 : ℝ) (992105058757/1000000000000 : ℝ) (496036822603/500000000000 : ℝ) (992073645207/1000000000000 : ℝ) (992089351981/1000000000000 : ℝ) (496044675991/500000000000 : ℝ) (62005584491/62500000000 : ℝ) (496044675929/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16689/131072 : ℝ)) 2 (992089351981/1000000000000 : ℝ) (496044675991/500000000000 : ℝ) (62005584491/62500000000 : ℝ) (496044675929/500000000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16689/131072 : ℝ)) 3 (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16689/131072 : ℝ)) 4 (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16689/131072 : ℝ)) 5 (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16689/131072 : ℝ)) 6 (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16689/131072 : ℝ)) 7 (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16689/131072 : ℝ))) (22125510087/125000000000 : ℝ) (88502040351/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16689/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22125510087/125000000000 : ℝ) (88502040351/500000000000 : ℝ) (147125510087/250000000000 : ℝ) (588502040351/1000000000000 : ℝ) (420718529061/1000000000000 : ℝ) (42071852907/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16689/131072 : ℝ))) 1 (147125510087/250000000000 : ℝ) (588502040351/1000000000000 : ℝ) (420718529061/1000000000000 : ℝ) (42071852907/100000000000 : ℝ) (15769071397/31250000000 : ℝ) (504610284711/1000000000000 : ℝ) (497587894511/1000000000000 : ℝ) (497587894519/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16689/131072 : ℝ))) 2 (15769071397/31250000000 : ℝ) (504610284711/1000000000000 : ℝ) (497587894511/1000000000000 : ℝ) (497587894519/1000000000000 : ℝ) (501099089607/1000000000000 : ℝ) (100219817923/200000000000 : ℝ) (250543394003/500000000000 : ℝ) (250543394007/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16689/131072 : ℝ))) 3 (501099089607/1000000000000 : ℝ) (100219817923/200000000000 : ℝ) (250543394003/500000000000 : ℝ) (250543394007/500000000000 : ℝ) (250546469403/500000000000 : ℝ) (100218587763/200000000000 : ℝ) (31318308673/62500000000 : ℝ) (501092938777/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16689/131072 : ℝ))) 4 (250546469403/500000000000 : ℝ) (100218587763/200000000000 : ℝ) (31318308673/62500000000 : ℝ) (501092938777/1000000000000 : ℝ) (501092938787/1000000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16689/131072 : ℝ))) 5 (501092938787/1000000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16689/131072 : ℝ))) 6 (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16689/131072 : ℝ))) 7 (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16689/131072 : ℝ)) hmem 8 (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16689/131072 : ℝ))) hcmem 8 (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16689/131072 : ℝ)) (496044675959/500000000000 : ℝ) (12401116899/12500000000 : ℝ) (250546469393/500000000000 : ℝ) (125273234699/250000000000 : ℝ) (79339118609/100000000000 : ℝ) (793391186109/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0683_exp_lower
  have heNumeric : (2054902153599/1000000000000 : ℝ)/4 ≤ Real.exp (-85256464400077/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902153599/1000000000000 : ℝ)/4 ≤ Real.exp ((66755/524288 : ℝ)-(793391186109/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66755/524288 : ℝ) (16689/131072 : ℝ) (793391186109/1000000000000 : ℝ) (2054902153599/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0684; no trusted numerical premise.
theorem cover8_leaf0684_exp_radius : (249503116033699993/250000000000000000 : ℝ) ≤ Real.exp ((-66757/4194304 : ℝ)/8) ∧ Real.exp ((-66757/4194304 : ℝ)/8) ≤ (998012464134799973/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66757/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0684_exp_lower : (230028370523644771/250000000000000000 : ℝ) ≤ Real.exp ((-21314116209471/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314116209471/32000000000000 : ℝ)/8) ≤ (184022696418915817/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314116209471/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0684_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490214657/100000000000 : ℝ) ≤ 4*Real.exp (16689/131072 : ℝ)*Real.exp (-mu (radius 8 (66757/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490214657/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66757/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0684_exp_radius
  have hrNumeric : (984209882859/1000000000000 : ℝ) ≤ Real.exp (-66757/4194304 : ℝ) ∧ Real.exp (-66757/4194304 : ℝ) ≤ (49210494143/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984209882859/1000000000000 : ℝ) ≤ (radius 8 (66757/524288 : ℝ)) ∧ (radius 8 (66757/524288 : ℝ)) ≤ (49210494143/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66757/524288 : ℝ)) (984209882859/1000000000000 : ℝ) (49210494143/50000000000 : ℝ) (11062836591/62500000000 : ℝ) (177005385463/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66757/524288 : ℝ)) (984209882859/1000000000000 : ℝ) (49210494143/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66757/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984209882859/1000000000000 : ℝ) (49210494143/50000000000 : ℝ) (992104941429/1000000000000 : ℝ) (99210494143/100000000000 : ℝ) (992073526941/1000000000000 : ℝ) (992073526943/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66757/524288 : ℝ)) 1 (992104941429/1000000000000 : ℝ) (99210494143/100000000000 : ℝ) (992073526941/1000000000000 : ℝ) (992073526943/1000000000000 : ℝ) (198417846837/200000000000 : ℝ) (992089234187/1000000000000 : ℝ) (49604461703/50000000000 : ℝ) (992089234063/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66757/524288 : ℝ)) 2 (198417846837/200000000000 : ℝ) (992089234187/1000000000000 : ℝ) (49604461703/50000000000 : ℝ) (992089234063/1000000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66757/524288 : ℝ)) 3 (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66757/524288 : ℝ)) 4 (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66757/524288 : ℝ)) 5 (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66757/524288 : ℝ)) 6 (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66757/524288 : ℝ)) 7 (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66757/524288 : ℝ))) (11062836591/62500000000 : ℝ) (177005385463/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66757/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11062836591/62500000000 : ℝ) (177005385463/1000000000000 : ℝ) (73562836591/125000000000 : ℝ) (147125673183/250000000000 : ℝ) (420720079691/1000000000000 : ℝ) (420720079701/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66757/524288 : ℝ))) 1 (73562836591/125000000000 : ℝ) (147125673183/250000000000 : ℝ) (420720079691/1000000000000 : ℝ) (420720079701/1000000000000 : ℝ) (504611386209/1000000000000 : ℝ) (504611386217/1000000000000 : ℝ) (248794543641/500000000000 : ℝ) (497589087291/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66757/524288 : ℝ))) 2 (504611386209/1000000000000 : ℝ) (504611386217/1000000000000 : ℝ) (248794543641/500000000000 : ℝ) (497589087291/1000000000000 : ℝ) (100220047349/200000000000 : ℝ) (250550118377/500000000000 : ℝ) (125271983873/250000000000 : ℝ) (501087935501/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66757/524288 : ℝ))) 3 (100220047349/200000000000 : ℝ) (250550118377/500000000000 : ℝ) (125271983873/250000000000 : ℝ) (501087935501/1000000000000 : ℝ) (250547043059/500000000000 : ℝ) (31318380383/62500000000 : ℝ) (1565919019/3125000000 : ℝ) (50109408609/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66757/524288 : ℝ))) 4 (250547043059/500000000000 : ℝ) (31318380383/62500000000 : ℝ) (1565919019/3125000000 : ℝ) (50109408609/100000000000 : ℝ) (501094086099/1000000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66757/524288 : ℝ))) 5 (501094086099/1000000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66757/524288 : ℝ))) 6 (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66757/524288 : ℝ))) 7 (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66757/524288 : ℝ)) hmem 8 (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66757/524288 : ℝ))) hcmem 8 (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66757/524288 : ℝ)) (496044617061/500000000000 : ℝ) (7936713873/8000000000 : ℝ) (250547043049/500000000000 : ℝ) (501094086109/1000000000000 : ℝ) (793393096857/1000000000000 : ℝ) (396696548439/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0684_exp_lower
  have heNumeric : (205490214657/100000000000 : ℝ)/4 ≤ Real.exp (-21314116209471/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490214657/100000000000 : ℝ)/4 ≤ Real.exp ((16689/131072 : ℝ)-(396696548439/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16689/131072 : ℝ) (66757/524288 : ℝ) (396696548439/500000000000 : ℝ) (205490214657/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0685; no trusted numerical premise.
theorem cover8_leaf0685_exp_radius : (249503108597927803/250000000000000000 : ℝ) ≤ Real.exp ((-33379/2097152 : ℝ)/8) ∧ Real.exp ((-33379/2097152 : ℝ)/8) ≤ (998012434391711213/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33379/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0685_exp_lower : (460056740851744311/500000000000000000 : ℝ) ≤ Real.exp ((-85256465273131/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256465273131/128000000000000 : ℝ)/8) ≤ (920113481703488623/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256465273131/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0685_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902139583/1000000000000 : ℝ) ≤ 4*Real.exp (66757/524288 : ℝ)*Real.exp (-mu (radius 8 (33379/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902139583/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33379/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0685_exp_radius
  have hrNumeric : (196841929641/200000000000 : ℝ) ≤ Real.exp (-33379/2097152 : ℝ) ∧ Real.exp (-33379/2097152 : ℝ) ≤ (492104824103/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196841929641/200000000000 : ℝ) ≤ (radius 8 (33379/262144 : ℝ)) ∧ (radius 8 (33379/262144 : ℝ)) ≤ (492104824103/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33379/262144 : ℝ)) (196841929641/200000000000 : ℝ) (492104824103/500000000000 : ℝ) (177006690207/1000000000000 : ℝ) (88503345107/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33379/262144 : ℝ)) (196841929641/200000000000 : ℝ) (492104824103/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33379/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196841929641/200000000000 : ℝ) (492104824103/500000000000 : ℝ) (496052412051/500000000000 : ℝ) (992104824103/1000000000000 : ℝ) (992073408677/1000000000000 : ℝ) (992073408679/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33379/262144 : ℝ)) 1 (496052412051/500000000000 : ℝ) (992104824103/1000000000000 : ℝ) (992073408677/1000000000000 : ℝ) (992073408679/1000000000000 : ℝ) (992089116389/1000000000000 : ℝ) (992089116391/1000000000000 : ℝ) (198417823253/200000000000 : ℝ) (992089116267/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33379/262144 : ℝ)) 2 (992089116389/1000000000000 : ℝ) (992089116391/1000000000000 : ℝ) (198417823253/200000000000 : ℝ) (992089116267/1000000000000 : ℝ) (992089116327/1000000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33379/262144 : ℝ)) 3 (992089116327/1000000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33379/262144 : ℝ)) 4 (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33379/262144 : ℝ)) 5 (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33379/262144 : ℝ)) 6 (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33379/262144 : ℝ)) 7 (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33379/262144 : ℝ))) (177006690207/1000000000000 : ℝ) (88503345107/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33379/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177006690207/1000000000000 : ℝ) (88503345107/500000000000 : ℝ) (588503345103/1000000000000 : ℝ) (588503345107/1000000000000 : ℝ) (84144326061/200000000000 : ℝ) (210360815157/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33379/262144 : ℝ))) 1 (588503345103/1000000000000 : ℝ) (588503345107/1000000000000 : ℝ) (84144326061/200000000000 : ℝ) (210360815157/500000000000 : ℝ) (63076560963/125000000000 : ℝ) (504612487711/1000000000000 : ℝ) (497590280041/1000000000000 : ℝ) (497590280049/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33379/262144 : ℝ))) 2 (63076560963/125000000000 : ℝ) (504612487711/1000000000000 : ℝ) (497590280041/1000000000000 : ℝ) (497590280049/1000000000000 : ℝ) (7829709123/15625000000 : ℝ) (12527534597/25000000000 : ℝ) (501089082967/1000000000000 : ℝ) (20043563319/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33379/262144 : ℝ))) 3 (7829709123/15625000000 : ℝ) (12527534597/25000000000 : ℝ) (501089082967/1000000000000 : ℝ) (20043563319/40000000000 : ℝ) (501095233419/1000000000000 : ℝ) (125273808357/250000000000 : ℝ) (501095233381/1000000000000 : ℝ) (50109523339/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33379/262144 : ℝ))) 4 (501095233419/1000000000000 : ℝ) (125273808357/250000000000 : ℝ) (501095233381/1000000000000 : ℝ) (50109523339/100000000000 : ℝ) (2505476167/5000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33379/262144 : ℝ))) 5 (2505476167/5000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33379/262144 : ℝ))) 6 (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33379/262144 : ℝ))) 7 (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33379/262144 : ℝ)) hmem 8 (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33379/262144 : ℝ))) hcmem 8 (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33379/262144 : ℝ)) (496044558163/500000000000 : ℝ) (992089116329/1000000000000 : ℝ) (501095233399/1000000000000 : ℝ) (501095233409/1000000000000 : ℝ) (793395007607/1000000000000 : ℝ) (793395007627/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0685_exp_lower
  have heNumeric : (2054902139583/1000000000000 : ℝ)/4 ≤ Real.exp (-85256465273131/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902139583/1000000000000 : ℝ)/4 ≤ Real.exp ((66757/524288 : ℝ)-(793395007627/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66757/524288 : ℝ) (33379/262144 : ℝ) (793395007627/1000000000000 : ℝ) (2054902139583/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0686; no trusted numerical premise.
theorem cover8_leaf0686_exp_radius : (499006202324311669/500000000000000000 : ℝ) ≤ Real.exp ((-66759/4194304 : ℝ)/8) ∧ Real.exp ((-66759/4194304 : ℝ)/8) ≤ (998012404648623339/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66759/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0686_exp_lower : (920113481314813459/1000000000000000000 : ℝ) ≤ Real.exp ((-8525646570569/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525646570569/12800000000000 : ℝ)/8) ≤ (46005674065740673/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525646570569/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0686_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902132639/1000000000000 : ℝ) ≤ 4*Real.exp (33379/262144 : ℝ)*Real.exp (-mu (radius 8 (66759/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902132639/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66759/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0686_exp_radius
  have hrNumeric : (984209413551/1000000000000 : ℝ) ≤ Real.exp (-66759/4194304 : ℝ) ∧ Real.exp (-66759/4194304 : ℝ) ≤ (61513088347/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984209413551/1000000000000 : ℝ) ≤ (radius 8 (66759/524288 : ℝ)) ∧ (radius 8 (66759/524288 : ℝ)) ≤ (61513088347/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66759/524288 : ℝ)) (984209413551/1000000000000 : ℝ) (61513088347/62500000000 : ℝ) (44251998737/250000000000 : ℝ) (88503997477/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66759/524288 : ℝ)) (984209413551/1000000000000 : ℝ) (61513088347/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66759/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984209413551/1000000000000 : ℝ) (61513088347/62500000000 : ℝ) (39684188271/40000000000 : ℝ) (124013088347/125000000000 : ℝ) (992073290413/1000000000000 : ℝ) (496036645207/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66759/524288 : ℝ)) 1 (39684188271/40000000000 : ℝ) (124013088347/125000000000 : ℝ) (992073290413/1000000000000 : ℝ) (496036645207/500000000000 : ℝ) (496044499297/500000000000 : ℝ) (198417799719/200000000000 : ℝ) (992088998469/1000000000000 : ℝ) (992088998471/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66759/524288 : ℝ)) 2 (496044499297/500000000000 : ℝ) (198417799719/200000000000 : ℝ) (992088998469/1000000000000 : ℝ) (992088998471/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66759/524288 : ℝ)) 3 (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66759/524288 : ℝ)) 4 (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66759/524288 : ℝ)) 5 (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66759/524288 : ℝ)) 6 (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66759/524288 : ℝ)) 7 (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66759/524288 : ℝ))) (44251998737/250000000000 : ℝ) (88503997477/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66759/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44251998737/250000000000 : ℝ) (88503997477/500000000000 : ℝ) (294251998737/500000000000 : ℝ) (588503997477/1000000000000 : ℝ) (420723180901/1000000000000 : ℝ) (420723180909/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66759/524288 : ℝ))) 1 (294251998737/500000000000 : ℝ) (588503997477/1000000000000 : ℝ) (420723180901/1000000000000 : ℝ) (420723180909/1000000000000 : ℝ) (504613589187/1000000000000 : ℝ) (504613589193/1000000000000 : ℝ) (248795736393/500000000000 : ℝ) (497591472793/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66759/524288 : ℝ))) 2 (504613589187/1000000000000 : ℝ) (504613589193/1000000000000 : ℝ) (248795736393/500000000000 : ℝ) (497591472793/1000000000000 : ℝ) (250551265493/500000000000 : ℝ) (501102530993/1000000000000 : ℝ) (501090230429/1000000000000 : ℝ) (125272557609/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66759/524288 : ℝ))) 3 (250551265493/500000000000 : ℝ) (501102530993/1000000000000 : ℝ) (501090230429/1000000000000 : ℝ) (125272557609/250000000000 : ℝ) (501096380707/1000000000000 : ℝ) (100219276143/200000000000 : ℝ) (501096380669/1000000000000 : ℝ) (501096380677/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66759/524288 : ℝ))) 4 (501096380707/1000000000000 : ℝ) (100219276143/200000000000 : ℝ) (501096380669/1000000000000 : ℝ) (501096380677/1000000000000 : ℝ) (31318523793/62500000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66759/524288 : ℝ))) 5 (31318523793/62500000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66759/524288 : ℝ))) 6 (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66759/524288 : ℝ))) 7 (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66759/524288 : ℝ)) hmem 8 (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66759/524288 : ℝ))) hcmem 8 (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66759/524288 : ℝ)) (992088998531/1000000000000 : ℝ) (992088998533/1000000000000 : ℝ) (501096380687/1000000000000 : ℝ) (62637047587/125000000000 : ℝ) (396698459169/500000000000 : ℝ) (158679383671/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0686_exp_lower
  have heNumeric : (2054902132639/1000000000000 : ℝ)/4 ≤ Real.exp (-8525646570569/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902132639/1000000000000 : ℝ)/4 ≤ Real.exp ((33379/262144 : ℝ)-(158679383671/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33379/262144 : ℝ) (66759/524288 : ℝ) (158679383671/200000000000 : ℝ) (2054902132639/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0687; no trusted numerical premise.
theorem cover8_leaf0687_exp_radius : (998012374905536351/1000000000000000000 : ℝ) ≤ Real.exp ((-8345/524288 : ℝ)/8) ∧ Real.exp ((-8345/524288 : ℝ)/8) ≤ (31187886715798011/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8345/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0687_exp_lower : (230028370232224659/250000000000000000 : ℝ) ≤ Real.exp ((-85256466135177/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256466135177/128000000000000 : ℝ)/8) ≤ (920113480928898637/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256466135177/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0687_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431382859/62500000000 : ℝ) ≤ 4*Real.exp (66759/524288 : ℝ)*Real.exp (-mu (radius 8 (8345/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (128431382859/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8345/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0687_exp_radius
  have hrNumeric : (492104589449/500000000000 : ℝ) ≤ Real.exp (-8345/524288 : ℝ) ∧ Real.exp (-8345/524288 : ℝ) ≤ (984209178899/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492104589449/500000000000 : ℝ) ≤ (radius 8 (8345/65536 : ℝ)) ∧ (radius 8 (8345/65536 : ℝ)) ≤ (984209178899/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8345/65536 : ℝ)) (492104589449/500000000000 : ℝ) (984209178899/1000000000000 : ℝ) (177009299673/1000000000000 : ℝ) (1106308123/6250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8345/65536 : ℝ)) (492104589449/500000000000 : ℝ) (984209178899/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8345/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492104589449/500000000000 : ℝ) (984209178899/1000000000000 : ℝ) (992104589449/1000000000000 : ℝ) (19842091789/20000000000 : ℝ) (992073172149/1000000000000 : ℝ) (19841463443/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8345/65536 : ℝ)) 1 (992104589449/1000000000000 : ℝ) (19842091789/20000000000 : ℝ) (992073172149/1000000000000 : ℝ) (19841463443/20000000000 : ℝ) (992088880799/1000000000000 : ℝ) (1240111101/1250000000 : ℝ) (496044440337/500000000000 : ℝ) (248022220169/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8345/65536 : ℝ)) 2 (992088880799/1000000000000 : ℝ) (1240111101/1250000000 : ℝ) (496044440337/500000000000 : ℝ) (248022220169/250000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8345/65536 : ℝ)) 3 (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8345/65536 : ℝ)) 4 (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8345/65536 : ℝ)) 5 (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8345/65536 : ℝ)) 6 (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8345/65536 : ℝ)) 7 (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8345/65536 : ℝ))) (177009299673/1000000000000 : ℝ) (1106308123/6250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8345/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177009299673/1000000000000 : ℝ) (1106308123/6250000000 : ℝ) (147126162459/250000000000 : ℝ) (7356308123/12500000000 : ℝ) (26295295717/62500000000 : ℝ) (210362365741/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8345/65536 : ℝ))) 1 (147126162459/250000000000 : ℝ) (7356308123/12500000000 : ℝ) (26295295717/62500000000 : ℝ) (210362365741/500000000000 : ℝ) (252307345327/500000000000 : ℝ) (504614690661/1000000000000 : ℝ) (62199083189/125000000000 : ℝ) (497592665521/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8345/65536 : ℝ))) 2 (252307345327/500000000000 : ℝ) (504614690661/1000000000000 : ℝ) (62199083189/125000000000 : ℝ) (497592665521/1000000000000 : ℝ) (501103678083/1000000000000 : ℝ) (501103678091/1000000000000 : ℝ) (501091377873/1000000000000 : ℝ) (250545688941/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8345/65536 : ℝ))) 3 (501103678083/1000000000000 : ℝ) (501103678091/1000000000000 : ℝ) (501091377873/1000000000000 : ℝ) (250545688941/500000000000 : ℝ) (250548763989/500000000000 : ℝ) (501097527987/1000000000000 : ℝ) (25054876397/50000000000 : ℝ) (501097527949/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8345/65536 : ℝ))) 4 (250548763989/500000000000 : ℝ) (501097527987/1000000000000 : ℝ) (25054876397/50000000000 : ℝ) (501097527949/1000000000000 : ℝ) (501097527959/1000000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8345/65536 : ℝ))) 5 (501097527959/1000000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8345/65536 : ℝ))) 6 (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8345/65536 : ℝ))) 7 (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8345/65536 : ℝ)) hmem 8 (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8345/65536 : ℝ))) hcmem 8 (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8345/65536 : ℝ)) (31002777523/31250000000 : ℝ) (496044440369/500000000000 : ℝ) (250548763979/500000000000 : ℝ) (15659297749/31250000000 : ℝ) (793398829041/1000000000000 : ℝ) (793398829059/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0687_exp_lower
  have heNumeric : (128431382859/62500000000 : ℝ)/4 ≤ Real.exp (-85256466135177/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431382859/62500000000 : ℝ)/4 ≤ Real.exp ((66759/524288 : ℝ)-(793398829059/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66759/524288 : ℝ) (8345/65536 : ℝ) (793398829059/1000000000000 : ℝ) (128431382859/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0688; no trusted numerical premise.
theorem cover8_leaf0688_exp_radius : (998012345162450251/1000000000000000000 : ℝ) ≤ Real.exp ((-66761/4194304 : ℝ)/8) ∧ Real.exp ((-66761/4194304 : ℝ)/8) ≤ (249503086290612563/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66761/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0688_exp_lower : (920113480544248969/1000000000000000000 : ℝ) ≤ Real.exp ((-10657058320407/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657058320407/16000000000000 : ℝ)/8) ≤ (92011348054424897/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657058320407/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0688_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902118871/1000000000000 : ℝ) ≤ 4*Real.exp (8345/65536 : ℝ)*Real.exp (-mu (radius 8 (66761/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902118871/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66761/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0688_exp_radius
  have hrNumeric : (246052236061/250000000000 : ℝ) ≤ Real.exp (-66761/4194304 : ℝ) ∧ Real.exp (-66761/4194304 : ℝ) ≤ (196841788849/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246052236061/250000000000 : ℝ) ≤ (radius 8 (66761/524288 : ℝ)) ∧ (radius 8 (66761/524288 : ℝ)) ≤ (196841788849/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66761/524288 : ℝ)) (246052236061/250000000000 : ℝ) (196841788849/200000000000 : ℝ) (88505302197/500000000000 : ℝ) (177010604401/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66761/524288 : ℝ)) (246052236061/250000000000 : ℝ) (196841788849/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66761/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246052236061/250000000000 : ℝ) (196841788849/200000000000 : ℝ) (496052236061/500000000000 : ℝ) (992104472123/1000000000000 : ℝ) (248018263471/250000000000 : ℝ) (496036526943/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66761/524288 : ℝ)) 1 (496052236061/500000000000 : ℝ) (992104472123/1000000000000 : ℝ) (248018263471/250000000000 : ℝ) (496036526943/500000000000 : ℝ) (992088763003/1000000000000 : ℝ) (198417752601/200000000000 : ℝ) (496044381439/500000000000 : ℝ) (992088762881/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66761/524288 : ℝ)) 2 (992088763003/1000000000000 : ℝ) (198417752601/200000000000 : ℝ) (496044381439/500000000000 : ℝ) (992088762881/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66761/524288 : ℝ)) 3 (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66761/524288 : ℝ)) 4 (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66761/524288 : ℝ)) 5 (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66761/524288 : ℝ)) 6 (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66761/524288 : ℝ)) 7 (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66761/524288 : ℝ))) (88505302197/500000000000 : ℝ) (177010604401/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66761/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88505302197/500000000000 : ℝ) (177010604401/1000000000000 : ℝ) (588505302197/1000000000000 : ℝ) (588505302201/1000000000000 : ℝ) (420726282033/1000000000000 : ℝ) (420726282043/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66761/524288 : ℝ))) 1 (588505302197/1000000000000 : ℝ) (588505302201/1000000000000 : ℝ) (420726282033/1000000000000 : ℝ) (420726282043/1000000000000 : ℝ) (100923158423/200000000000 : ℝ) (252307896061/500000000000 : ℝ) (497593858231/1000000000000 : ℝ) (1554980807/3125000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66761/524288 : ℝ))) 2 (100923158423/200000000000 : ℝ) (252307896061/500000000000 : ℝ) (497593858231/1000000000000 : ℝ) (1554980807/3125000000 : ℝ) (501104825173/1000000000000 : ℝ) (501104825181/1000000000000 : ℝ) (501092525311/1000000000000 : ℝ) (12527313133/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66761/524288 : ℝ))) 3 (501104825173/1000000000000 : ℝ) (501104825181/1000000000000 : ℝ) (501092525311/1000000000000 : ℝ) (12527313133/25000000000 : ℝ) (250549337621/500000000000 : ℝ) (501098675251/1000000000000 : ℝ) (125274668801/250000000000 : ℝ) (501098675213/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66761/524288 : ℝ))) 4 (250549337621/500000000000 : ℝ) (501098675251/1000000000000 : ℝ) (125274668801/250000000000 : ℝ) (501098675213/1000000000000 : ℝ) (501098675223/1000000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66761/524288 : ℝ))) 5 (501098675223/1000000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66761/524288 : ℝ))) 6 (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66761/524288 : ℝ))) 7 (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66761/524288 : ℝ)) hmem 8 (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66761/524288 : ℝ))) hcmem 8 (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66761/524288 : ℝ)) (49604438147/50000000000 : ℝ) (992088762943/1000000000000 : ℝ) (250549337611/500000000000 : ℝ) (15659333601/31250000000 : ℝ) (793400739733/1000000000000 : ℝ) (99175092469/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0688_exp_lower
  have heNumeric : (2054902118871/1000000000000 : ℝ)/4 ≤ Real.exp (-10657058320407/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902118871/1000000000000 : ℝ)/4 ≤ Real.exp ((8345/65536 : ℝ)-(99175092469/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8345/65536 : ℝ) (66761/524288 : ℝ) (99175092469/125000000000 : ℝ) (2054902118871/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0689; no trusted numerical premise.
theorem cover8_leaf0689_exp_radius : (249503078854841259/250000000000000000 : ℝ) ≤ Real.exp ((-33381/2097152 : ℝ)/8) ∧ Real.exp ((-33381/2097152 : ℝ)/8) ≤ (998012315419365037/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33381/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0689_exp_lower : (230028370040446143/250000000000000000 : ℝ) ≤ Real.exp ((-85256466988903/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256466988903/128000000000000 : ℝ)/8) ≤ (920113480161784573/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256466988903/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0689_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451056019/500000000000 : ℝ) ≤ 4*Real.exp (66761/524288 : ℝ)*Real.exp (-mu (radius 8 (33381/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451056019/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33381/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0689_exp_radius
  have hrNumeric : (98420870959/100000000000 : ℝ) ≤ Real.exp (-33381/2097152 : ℝ) ∧ Real.exp (-33381/2097152 : ℝ) ≤ (984208709591/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98420870959/100000000000 : ℝ) ≤ (radius 8 (33381/262144 : ℝ)) ∧ (radius 8 (33381/262144 : ℝ)) ≤ (984208709591/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33381/262144 : ℝ)) (98420870959/100000000000 : ℝ) (984208709591/1000000000000 : ℝ) (35402381821/200000000000 : ℝ) (22126488639/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33381/262144 : ℝ)) (98420870959/100000000000 : ℝ) (984208709591/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33381/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98420870959/100000000000 : ℝ) (984208709591/1000000000000 : ℝ) (198420870959/200000000000 : ℝ) (248026088699/250000000000 : ℝ) (49603646781/50000000000 : ℝ) (992072935621/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33381/262144 : ℝ)) 1 (198420870959/200000000000 : ℝ) (248026088699/250000000000 : ℝ) (49603646781/50000000000 : ℝ) (992072935621/1000000000000 : ℝ) (992088645207/1000000000000 : ℝ) (992088645209/1000000000000 : ℝ) (992088645083/1000000000000 : ℝ) (198417729017/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33381/262144 : ℝ)) 2 (992088645207/1000000000000 : ℝ) (992088645209/1000000000000 : ℝ) (992088645083/1000000000000 : ℝ) (198417729017/200000000000 : ℝ) (198417729029/200000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33381/262144 : ℝ)) 3 (198417729029/200000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33381/262144 : ℝ)) 4 (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33381/262144 : ℝ)) 5 (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33381/262144 : ℝ)) 6 (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33381/262144 : ℝ)) 7 (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33381/262144 : ℝ))) (35402381821/200000000000 : ℝ) (22126488639/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33381/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35402381821/200000000000 : ℝ) (22126488639/125000000000 : ℝ) (73563244319/125000000000 : ℝ) (147126488639/250000000000 : ℝ) (420727832577/1000000000000 : ℝ) (210363916293/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33381/262144 : ℝ))) 1 (73563244319/125000000000 : ℝ) (147126488639/250000000000 : ℝ) (420727832577/1000000000000 : ℝ) (210363916293/500000000000 : ℝ) (126154223391/250000000000 : ℝ) (504616893571/1000000000000 : ℝ) (497595050937/1000000000000 : ℝ) (99519010189/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33381/262144 : ℝ))) 2 (126154223391/250000000000 : ℝ) (504616893571/1000000000000 : ℝ) (497595050937/1000000000000 : ℝ) (99519010189/200000000000 : ℝ) (2004423889/4000000000 : ℝ) (250552986129/500000000000 : ℝ) (15659177273/31250000000 : ℝ) (100218734549/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33381/262144 : ℝ))) 3 (2004423889/4000000000 : ℝ) (250552986129/500000000000 : ℝ) (15659177273/31250000000 : ℝ) (100218734549/200000000000 : ℝ) (501099822493/1000000000000 : ℝ) (250549911251/500000000000 : ℝ) (100219964491/200000000000 : ℝ) (3914842363/7812500000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33381/262144 : ℝ))) 4 (501099822493/1000000000000 : ℝ) (250549911251/500000000000 : ℝ) (100219964491/200000000000 : ℝ) (3914842363/7812500000 : ℝ) (250549911237/500000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33381/262144 : ℝ))) 5 (250549911237/500000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33381/262144 : ℝ))) 6 (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33381/262144 : ℝ))) 7 (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33381/262144 : ℝ)) hmem 8 (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33381/262144 : ℝ))) hcmem 8 (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33381/262144 : ℝ)) (124011080643/125000000000 : ℝ) (992088645147/1000000000000 : ℝ) (501099822473/1000000000000 : ℝ) (501099822483/1000000000000 : ℝ) (396701325203/500000000000 : ℝ) (396701325213/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0689_exp_lower
  have heNumeric : (1027451056019/500000000000 : ℝ)/4 ≤ Real.exp (-85256466988903/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451056019/500000000000 : ℝ)/4 ≤ Real.exp ((66761/524288 : ℝ)-(396701325213/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66761/524288 : ℝ) (33381/262144 : ℝ) (396701325213/500000000000 : ℝ) (1027451056019/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0690; no trusted numerical premise.
theorem cover8_leaf0690_exp_radius : (998012285676280709/1000000000000000000 : ℝ) ≤ Real.exp ((-66763/4194304 : ℝ)/8) ∧ Real.exp ((-66763/4194304 : ℝ)/8) ≤ (99801228567628071/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66763/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0690_exp_lower : (920113479782655587/1000000000000000000 : ℝ) ≤ Real.exp ((-42628233705419/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628233705419/64000000000000 : ℝ)/8) ≤ (230028369945663897/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628233705419/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0690_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431381579/62500000000 : ℝ) ≤ 4*Real.exp (33381/262144 : ℝ)*Real.exp (-mu (radius 8 (66763/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431381579/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66763/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0690_exp_radius
  have hrNumeric : (984208474937/1000000000000 : ℝ) ≤ Real.exp (-66763/4194304 : ℝ) ∧ Real.exp (-66763/4194304 : ℝ) ≤ (492104237469/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984208474937/1000000000000 : ℝ) ≤ (radius 8 (66763/524288 : ℝ)) ∧ (radius 8 (66763/524288 : ℝ)) ≤ (492104237469/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66763/524288 : ℝ)) (984208474937/1000000000000 : ℝ) (492104237469/500000000000 : ℝ) (177013213801/1000000000000 : ℝ) (177013213807/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66763/524288 : ℝ)) (984208474937/1000000000000 : ℝ) (492104237469/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66763/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984208474937/1000000000000 : ℝ) (492104237469/500000000000 : ℝ) (248026059367/250000000000 : ℝ) (992104237469/1000000000000 : ℝ) (248018204339/250000000000 : ℝ) (992072817357/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66763/524288 : ℝ)) 1 (248026059367/250000000000 : ℝ) (992104237469/1000000000000 : ℝ) (248018204339/250000000000 : ℝ) (992072817357/1000000000000 : ℝ) (248022131853/250000000000 : ℝ) (992088527413/1000000000000 : ℝ) (992088527287/1000000000000 : ℝ) (992088527289/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66763/524288 : ℝ)) 2 (248022131853/250000000000 : ℝ) (992088527413/1000000000000 : ℝ) (992088527287/1000000000000 : ℝ) (992088527289/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66763/524288 : ℝ)) 3 (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66763/524288 : ℝ)) 4 (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66763/524288 : ℝ)) 5 (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66763/524288 : ℝ)) 6 (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66763/524288 : ℝ)) 7 (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66763/524288 : ℝ))) (177013213801/1000000000000 : ℝ) (177013213807/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66763/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177013213801/1000000000000 : ℝ) (177013213807/1000000000000 : ℝ) (5885066069/10000000000 : ℝ) (73563325863/125000000000 : ℝ) (52591172887/125000000000 : ℝ) (6573896611/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66763/524288 : ℝ))) 1 (5885066069/10000000000 : ℝ) (73563325863/125000000000 : ℝ) (52591172887/125000000000 : ℝ) (6573896611/15625000000 : ℝ) (252308997499/500000000000 : ℝ) (126154498751/250000000000 : ℝ) (62199530453/125000000000 : ℝ) (497596243631/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66763/524288 : ℝ))) 2 (252308997499/500000000000 : ℝ) (126154498751/250000000000 : ℝ) (62199530453/125000000000 : ℝ) (497596243631/1000000000000 : ℝ) (501107119311/1000000000000 : ℝ) (250553559659/500000000000 : ℝ) (31318426259/62500000000 : ℝ) (62636852519/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66763/524288 : ℝ))) 3 (501107119311/1000000000000 : ℝ) (250553559659/500000000000 : ℝ) (31318426259/62500000000 : ℝ) (62636852519/125000000000 : ℝ) (501100969727/1000000000000 : ℝ) (100220193947/200000000000 : ℝ) (501100969689/1000000000000 : ℝ) (250550484849/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66763/524288 : ℝ))) 4 (501100969727/1000000000000 : ℝ) (100220193947/200000000000 : ℝ) (501100969689/1000000000000 : ℝ) (250550484849/500000000000 : ℝ) (125275242427/250000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66763/524288 : ℝ))) 5 (125275242427/250000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66763/524288 : ℝ))) 6 (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66763/524288 : ℝ))) 7 (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66763/524288 : ℝ)) hmem 8 (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66763/524288 : ℝ))) hcmem 8 (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66763/524288 : ℝ)) (992088527349/1000000000000 : ℝ) (992088527351/1000000000000 : ℝ) (501100969707/1000000000000 : ℝ) (501100969717/1000000000000 : ℝ) (793404561053/1000000000000 : ℝ) (793404561071/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0690_exp_lower
  have heNumeric : (128431381579/62500000000 : ℝ)/4 ≤ Real.exp (-42628233705419/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431381579/62500000000 : ℝ)/4 ≤ Real.exp ((33381/262144 : ℝ)-(793404561071/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33381/262144 : ℝ) (66763/524288 : ℝ) (793404561071/1000000000000 : ℝ) (128431381579/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0691; no trusted numerical premise.
theorem cover8_leaf0691_exp_radius : (998012255933197267/1000000000000000000 : ℝ) ≤ Real.exp ((-16691/1048576 : ℝ)/8) ∧ Real.exp ((-16691/1048576 : ℝ)/8) ≤ (249503063983299317/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16691/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0691_exp_lower : (920113479404676743/1000000000000000000 : ℝ) ≤ Real.exp ((-85256467831493/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256467831493/128000000000000 : ℝ)/8) ≤ (115014184925584593/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256467831493/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0691_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902098511/1000000000000 : ℝ) ≤ 4*Real.exp (66763/524288 : ℝ)*Real.exp (-mu (radius 8 (16691/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902098511/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16691/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0691_exp_radius
  have hrNumeric : (984208240283/1000000000000 : ℝ) ≤ Real.exp (-16691/1048576 : ℝ) ∧ Real.exp (-16691/1048576 : ℝ) ≤ (246052060071/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984208240283/1000000000000 : ℝ) ≤ (radius 8 (16691/131072 : ℝ)) ∧ (radius 8 (16691/131072 : ℝ)) ≤ (246052060071/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16691/131072 : ℝ)) (984208240283/1000000000000 : ℝ) (246052060071/250000000000 : ℝ) (44253629623/250000000000 : ℝ) (88507259249/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16691/131072 : ℝ)) (984208240283/1000000000000 : ℝ) (246052060071/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16691/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984208240283/1000000000000 : ℝ) (246052060071/250000000000 : ℝ) (992104120141/1000000000000 : ℝ) (496052060071/500000000000 : ℝ) (992072699091/1000000000000 : ℝ) (992072699093/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16691/131072 : ℝ)) 1 (992104120141/1000000000000 : ℝ) (496052060071/500000000000 : ℝ) (992072699091/1000000000000 : ℝ) (992072699093/1000000000000 : ℝ) (62005525601/62500000000 : ℝ) (496044204809/500000000000 : ℝ) (992088409491/1000000000000 : ℝ) (496044204747/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16691/131072 : ℝ)) 2 (62005525601/62500000000 : ℝ) (496044204809/500000000000 : ℝ) (992088409491/1000000000000 : ℝ) (496044204747/500000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16691/131072 : ℝ)) 3 (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16691/131072 : ℝ)) 4 (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16691/131072 : ℝ)) 5 (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16691/131072 : ℝ)) 6 (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16691/131072 : ℝ)) 7 (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16691/131072 : ℝ))) (44253629623/250000000000 : ℝ) (88507259249/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16691/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44253629623/250000000000 : ℝ) (88507259249/500000000000 : ℝ) (294253629623/500000000000 : ℝ) (588507259249/1000000000000 : ℝ) (105182733401/250000000000 : ℝ) (105182733403/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16691/131072 : ℝ))) 1 (294253629623/500000000000 : ℝ) (588507259249/1000000000000 : ℝ) (105182733401/250000000000 : ℝ) (105182733403/250000000000 : ℝ) (20184763857/40000000000 : ℝ) (504619096431/1000000000000 : ℝ) (248798718151/500000000000 : ℝ) (497597436309/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16691/131072 : ℝ))) 2 (20184763857/40000000000 : ℝ) (504619096431/1000000000000 : ℝ) (248798718151/500000000000 : ℝ) (497597436309/1000000000000 : ℝ) (501108266363/1000000000000 : ℝ) (50110826637/100000000000 : ℝ) (100219193509/200000000000 : ℝ) (7829624493/15625000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16691/131072 : ℝ))) 3 (501108266363/1000000000000 : ℝ) (50110826637/100000000000 : ℝ) (100219193509/200000000000 : ℝ) (7829624493/15625000000 : ℝ) (250551058477/500000000000 : ℝ) (501102116961/1000000000000 : ℝ) (125275529229/250000000000 : ℝ) (125275529231/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16691/131072 : ℝ))) 4 (250551058477/500000000000 : ℝ) (501102116961/1000000000000 : ℝ) (125275529229/250000000000 : ℝ) (125275529231/250000000000 : ℝ) (100220423387/200000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16691/131072 : ℝ))) 5 (100220423387/200000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16691/131072 : ℝ))) 6 (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16691/131072 : ℝ))) 7 (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16691/131072 : ℝ)) hmem 8 (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16691/131072 : ℝ))) hcmem 8 (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16691/131072 : ℝ)) (992088409553/1000000000000 : ℝ) (248022102389/250000000000 : ℝ) (250551058467/500000000000 : ℝ) (501102116943/1000000000000 : ℝ) (99175808961/125000000000 : ℝ) (396703235853/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0691_exp_lower
  have heNumeric : (2054902098511/1000000000000 : ℝ)/4 ≤ Real.exp (-85256467831493/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902098511/1000000000000 : ℝ)/4 ≤ Real.exp ((66763/524288 : ℝ)-(396703235853/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66763/524288 : ℝ) (16691/131072 : ℝ) (396703235853/500000000000 : ℝ) (2054902098511/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0692; no trusted numerical premise.
theorem cover8_leaf0692_exp_radius : (124751528273764339/125000000000000000 : ℝ) ≤ Real.exp ((-66765/4194304 : ℝ)/8) ∧ Real.exp ((-66765/4194304 : ℝ)/8) ≤ (998012226190114713/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66765/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0692_exp_lower : (230028369757422067/250000000000000000 : ℝ) ≤ Real.exp ((-4262823412441/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262823412441/6400000000000 : ℝ)/8) ≤ (920113479029688269/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262823412441/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0692_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902091811/1000000000000 : ℝ) ≤ 4*Real.exp (16691/131072 : ℝ)*Real.exp (-mu (radius 8 (66765/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902091811/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66765/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0692_exp_radius
  have hrNumeric : (98420800563/100000000000 : ℝ) ≤ Real.exp (-66765/4194304 : ℝ) ∧ Real.exp (-66765/4194304 : ℝ) ≤ (984208005631/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98420800563/100000000000 : ℝ) ≤ (radius 8 (66765/524288 : ℝ)) ∧ (radius 8 (66765/524288 : ℝ)) ≤ (984208005631/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66765/524288 : ℝ)) (98420800563/100000000000 : ℝ) (984208005631/1000000000000 : ℝ) (2765872237/15625000000 : ℝ) (88507911587/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66765/524288 : ℝ)) (98420800563/100000000000 : ℝ) (984208005631/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66765/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98420800563/100000000000 : ℝ) (984208005631/1000000000000 : ℝ) (198420800563/200000000000 : ℝ) (3875406261/3906250000 : ℝ) (992072580827/1000000000000 : ℝ) (992072580829/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66765/524288 : ℝ)) 1 (198420800563/200000000000 : ℝ) (3875406261/3906250000 : ℝ) (992072580827/1000000000000 : ℝ) (992072580829/1000000000000 : ℝ) (992088291821/1000000000000 : ℝ) (992088291823/1000000000000 : ℝ) (62005518231/62500000000 : ℝ) (992088291699/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66765/524288 : ℝ)) 2 (992088291821/1000000000000 : ℝ) (992088291823/1000000000000 : ℝ) (62005518231/62500000000 : ℝ) (992088291699/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66765/524288 : ℝ)) 3 (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66765/524288 : ℝ)) 4 (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66765/524288 : ℝ)) 5 (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66765/524288 : ℝ)) 6 (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66765/524288 : ℝ)) 7 (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66765/524288 : ℝ))) (2765872237/15625000000 : ℝ) (88507911587/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66765/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (2765872237/15625000000 : ℝ) (88507911587/500000000000 : ℝ) (18390872237/31250000000 : ℝ) (588507911587/1000000000000 : ℝ) (420732484089/1000000000000 : ℝ) (420732484097/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66765/524288 : ℝ))) 1 (18390872237/31250000000 : ℝ) (588507911587/1000000000000 : ℝ) (420732484089/1000000000000 : ℝ) (420732484097/1000000000000 : ℝ) (126155049459/250000000000 : ℝ) (252310098921/500000000000 : ℝ) (497598628963/1000000000000 : ℝ) (49759862897/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66765/524288 : ℝ))) 2 (126155049459/250000000000 : ℝ) (252310098921/500000000000 : ℝ) (497598628963/1000000000000 : ℝ) (49759862897/100000000000 : ℝ) (501109413399/1000000000000 : ℝ) (250554706703/500000000000 : ℝ) (501097114929/1000000000000 : ℝ) (62637139367/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66765/524288 : ℝ))) 3 (501109413399/1000000000000 : ℝ) (250554706703/500000000000 : ℝ) (501097114929/1000000000000 : ℝ) (62637139367/125000000000 : ℝ) (125275816041/250000000000 : ℝ) (501103264171/1000000000000 : ℝ) (250551632063/500000000000 : ℝ) (250551632067/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66765/524288 : ℝ))) 4 (125275816041/250000000000 : ℝ) (501103264171/1000000000000 : ℝ) (250551632063/500000000000 : ℝ) (250551632067/500000000000 : ℝ) (100220652829/200000000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66765/524288 : ℝ))) 5 (100220652829/200000000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66765/524288 : ℝ))) 6 (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66765/524288 : ℝ))) 7 (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66765/524288 : ℝ)) hmem 8 (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66765/524288 : ℝ))) hcmem 8 (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66765/524288 : ℝ)) (496044145879/500000000000 : ℝ) (992088291761/1000000000000 : ℝ) (31318954009/62500000000 : ℝ) (501103264153/1000000000000 : ℝ) (793408382297/1000000000000 : ℝ) (158681676463/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0692_exp_lower
  have heNumeric : (2054902091811/1000000000000 : ℝ)/4 ≤ Real.exp (-4262823412441/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902091811/1000000000000 : ℝ)/4 ≤ Real.exp ((16691/131072 : ℝ)-(158681676463/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16691/131072 : ℝ) (66765/524288 : ℝ) (158681676463/200000000000 : ℝ) (2054902091811/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0693; no trusted numerical premise.
theorem cover8_leaf0693_exp_radius : (249503049111758261/250000000000000000 : ℝ) ≤ Real.exp ((-33383/2097152 : ℝ)/8) ∧ Real.exp ((-33383/2097152 : ℝ)/8) ≤ (199602439289406609/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33383/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0693_exp_lower : (57507092415990621/62500000000000000 : ℝ) ≤ Real.exp ((-85256468664867/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256468664867/128000000000000 : ℝ)/8) ≤ (920113478655849937/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256468664867/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0693_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725521283/250000000000 : ℝ) ≤ 4*Real.exp (66765/524288 : ℝ)*Real.exp (-mu (radius 8 (33383/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725521283/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33383/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0693_exp_radius
  have hrNumeric : (30756492843/31250000000 : ℝ) ≤ Real.exp (-33383/2097152 : ℝ) ∧ Real.exp (-33383/2097152 : ℝ) ≤ (984207770977/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (30756492843/31250000000 : ℝ) ≤ (radius 8 (33383/262144 : ℝ)) ∧ (radius 8 (33383/262144 : ℝ)) ≤ (984207770977/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33383/262144 : ℝ)) (30756492843/31250000000 : ℝ) (984207770977/1000000000000 : ℝ) (177017127839/1000000000000 : ℝ) (35403425569/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33383/262144 : ℝ)) (30756492843/31250000000 : ℝ) (984207770977/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33383/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (30756492843/31250000000 : ℝ) (984207770977/1000000000000 : ℝ) (62006492843/62500000000 : ℝ) (992103885489/1000000000000 : ℝ) (992072462563/1000000000000 : ℝ) (248018115641/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33383/262144 : ℝ)) 1 (62006492843/62500000000 : ℝ) (992103885489/1000000000000 : ℝ) (992072462563/1000000000000 : ℝ) (248018115641/250000000000 : ℝ) (39683526961/40000000000 : ℝ) (992088174027/1000000000000 : ℝ) (992088173901/1000000000000 : ℝ) (992088173903/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33383/262144 : ℝ)) 2 (39683526961/40000000000 : ℝ) (992088174027/1000000000000 : ℝ) (992088173901/1000000000000 : ℝ) (992088173903/1000000000000 : ℝ) (992088173963/1000000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33383/262144 : ℝ)) 3 (992088173963/1000000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33383/262144 : ℝ)) 4 (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33383/262144 : ℝ)) 5 (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33383/262144 : ℝ)) 6 (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33383/262144 : ℝ)) 7 (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33383/262144 : ℝ))) (177017127839/1000000000000 : ℝ) (35403425569/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33383/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177017127839/1000000000000 : ℝ) (35403425569/200000000000 : ℝ) (588508563919/1000000000000 : ℝ) (588508563923/1000000000000 : ℝ) (210367017281/500000000000 : ℝ) (42073403457/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33383/262144 : ℝ))) 1 (588508563919/1000000000000 : ℝ) (588508563923/1000000000000 : ℝ) (210367017281/500000000000 : ℝ) (42073403457/100000000000 : ℝ) (12615532481/25000000000 : ℝ) (504621299247/1000000000000 : ℝ) (99519964323/200000000000 : ℝ) (497599821623/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33383/262144 : ℝ))) 2 (12615532481/25000000000 : ℝ) (504621299247/1000000000000 : ℝ) (99519964323/200000000000 : ℝ) (497599821623/1000000000000 : ℝ) (501110560427/1000000000000 : ℝ) (100222112087/200000000000 : ℝ) (15659320697/31250000000 : ℝ) (501098262313/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33383/262144 : ℝ))) 3 (501110560427/1000000000000 : ℝ) (100222112087/200000000000 : ℝ) (15659320697/31250000000 : ℝ) (501098262313/1000000000000 : ℝ) (100220882273/200000000000 : ℝ) (250552205687/500000000000 : ℝ) (501104411327/1000000000000 : ℝ) (501104411337/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33383/262144 : ℝ))) 4 (100220882273/200000000000 : ℝ) (250552205687/500000000000 : ℝ) (501104411327/1000000000000 : ℝ) (501104411337/1000000000000 : ℝ) (250552205673/500000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33383/262144 : ℝ))) 5 (250552205673/500000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33383/262144 : ℝ))) 6 (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33383/262144 : ℝ))) 7 (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33383/262144 : ℝ)) hmem 8 (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33383/262144 : ℝ))) hcmem 8 (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33383/262144 : ℝ)) (496044086981/500000000000 : ℝ) (198417634793/200000000000 : ℝ) (100220882269/200000000000 : ℝ) (125276102839/250000000000 : ℝ) (793410292893/1000000000000 : ℝ) (396705146457/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0693_exp_lower
  have heNumeric : (513725521283/250000000000 : ℝ)/4 ≤ Real.exp (-85256468664867/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725521283/250000000000 : ℝ)/4 ≤ Real.exp ((66765/524288 : ℝ)-(396705146457/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66765/524288 : ℝ) (33383/262144 : ℝ) (396705146457/500000000000 : ℝ) (513725521283/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0694; no trusted numerical premise.
theorem cover8_leaf0694_exp_radius : (998012166703952261/1000000000000000000 : ℝ) ≤ Real.exp ((-66767/4194304 : ℝ)/8) ∧ Real.exp ((-66767/4194304 : ℝ)/8) ≤ (499006083351976131/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66767/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0694_exp_lower : (920113478285577043/1000000000000000000 : ℝ) ≤ Real.exp ((-42628234538473/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628234538473/64000000000000 : ℝ)/8) ≤ (230028369571394261/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628234538473/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0694_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902078517/1000000000000 : ℝ) ≤ 4*Real.exp (33383/262144 : ℝ)*Real.exp (-mu (radius 8 (66767/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902078517/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66767/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0694_exp_radius
  have hrNumeric : (984207536323/1000000000000 : ℝ) ≤ Real.exp (-66767/4194304 : ℝ) ∧ Real.exp (-66767/4194304 : ℝ) ≤ (246051884081/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984207536323/1000000000000 : ℝ) ≤ (radius 8 (66767/524288 : ℝ)) ∧ (radius 8 (66767/524288 : ℝ)) ≤ (246051884081/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66767/524288 : ℝ)) (984207536323/1000000000000 : ℝ) (246051884081/250000000000 : ℝ) (35403686499/200000000000 : ℝ) (177018432501/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66767/524288 : ℝ)) (984207536323/1000000000000 : ℝ) (246051884081/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66767/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984207536323/1000000000000 : ℝ) (246051884081/250000000000 : ℝ) (992103768161/1000000000000 : ℝ) (496051884081/500000000000 : ℝ) (992072344299/1000000000000 : ℝ) (9920723443/10000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66767/524288 : ℝ)) 1 (992103768161/1000000000000 : ℝ) (496051884081/500000000000 : ℝ) (992072344299/1000000000000 : ℝ) (9920723443/10000000000 : ℝ) (99208805623/100000000000 : ℝ) (992088056231/1000000000000 : ℝ) (198417611221/200000000000 : ℝ) (992088056107/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66767/524288 : ℝ)) 2 (99208805623/100000000000 : ℝ) (992088056231/1000000000000 : ℝ) (198417611221/200000000000 : ℝ) (992088056107/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66767/524288 : ℝ)) 3 (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66767/524288 : ℝ)) 4 (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66767/524288 : ℝ)) 5 (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66767/524288 : ℝ)) 6 (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66767/524288 : ℝ)) 7 (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66767/524288 : ℝ))) (35403686499/200000000000 : ℝ) (177018432501/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66767/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35403686499/200000000000 : ℝ) (177018432501/1000000000000 : ℝ) (588509216247/1000000000000 : ℝ) (588509216251/1000000000000 : ℝ) (420735585011/1000000000000 : ℝ) (420735585019/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66767/524288 : ℝ))) 1 (588509216247/1000000000000 : ℝ) (588509216251/1000000000000 : ℝ) (420735585011/1000000000000 : ℝ) (420735585019/1000000000000 : ℝ) (504622400629/1000000000000 : ℝ) (100924480127/200000000000 : ℝ) (497601014249/1000000000000 : ℝ) (31100063391/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66767/524288 : ℝ))) 2 (504622400629/1000000000000 : ℝ) (100924480127/200000000000 : ℝ) (497601014249/1000000000000 : ℝ) (31100063391/62500000000 : ℝ) (501111707439/1000000000000 : ℝ) (250555853723/500000000000 : ℝ) (1957419569/3906250000 : ℝ) (501099409671/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66767/524288 : ℝ))) 3 (501111707439/1000000000000 : ℝ) (250555853723/500000000000 : ℝ) (1957419569/3906250000 : ℝ) (501099409671/1000000000000 : ℝ) (501105558551/1000000000000 : ℝ) (501105558559/1000000000000 : ℝ) (501105558513/1000000000000 : ℝ) (501105558521/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66767/524288 : ℝ))) 4 (501105558551/1000000000000 : ℝ) (501105558559/1000000000000 : ℝ) (501105558513/1000000000000 : ℝ) (501105558521/1000000000000 : ℝ) (125276389633/250000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66767/524288 : ℝ))) 5 (125276389633/250000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66767/524288 : ℝ))) 6 (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66767/524288 : ℝ))) 7 (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66767/524288 : ℝ)) hmem 8 (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66767/524288 : ℝ))) hcmem 8 (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66767/524288 : ℝ)) (992088056167/1000000000000 : ℝ) (992088056169/1000000000000 : ℝ) (501105558531/1000000000000 : ℝ) (25055277927/50000000000 : ℝ) (158682440693/200000000000 : ℝ) (396706101741/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0694_exp_lower
  have heNumeric : (2054902078517/1000000000000 : ℝ)/4 ≤ Real.exp (-42628234538473/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902078517/1000000000000 : ℝ)/4 ≤ Real.exp ((33383/262144 : ℝ)-(396706101741/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33383/262144 : ℝ) (66767/524288 : ℝ) (396706101741/500000000000 : ℝ) (2054902078517/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0695; no trusted numerical premise.
theorem cover8_leaf0695_exp_radius : (499006068480436183/500000000000000000 : ℝ) ≤ Real.exp ((-4173/262144 : ℝ)/8) ∧ Real.exp ((-4173/262144 : ℝ)/8) ≤ (998012136960872367/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4173/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0695_exp_lower : (230028369478998559/250000000000000000 : ℝ) ≤ Real.exp ((-85256469488257/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256469488257/128000000000000 : ℝ)/8) ≤ (920113477915994237/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256469488257/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0695_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902071913/1000000000000 : ℝ) ≤ 4*Real.exp (66767/524288 : ℝ)*Real.exp (-mu (radius 8 (4173/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902071913/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4173/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0695_exp_radius
  have hrNumeric : (984207301669/1000000000000 : ℝ) ≤ Real.exp (-4173/262144 : ℝ) ∧ Real.exp (-4173/262144 : ℝ) ≤ (98420730167/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984207301669/1000000000000 : ℝ) ≤ (radius 8 (4173/32768 : ℝ)) ∧ (radius 8 (4173/32768 : ℝ)) ≤ (98420730167/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4173/32768 : ℝ)) (984207301669/1000000000000 : ℝ) (98420730167/100000000000 : ℝ) (88509868573/500000000000 : ℝ) (177019737153/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4173/32768 : ℝ)) (984207301669/1000000000000 : ℝ) (98420730167/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4173/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984207301669/1000000000000 : ℝ) (98420730167/100000000000 : ℝ) (496051825417/500000000000 : ℝ) (198420730167/200000000000 : ℝ) (496036113017/500000000000 : ℝ) (198414445207/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4173/32768 : ℝ)) 1 (496051825417/500000000000 : ℝ) (198420730167/200000000000 : ℝ) (496036113017/500000000000 : ℝ) (198414445207/200000000000 : ℝ) (496043969217/500000000000 : ℝ) (198417587687/200000000000 : ℝ) (992087938309/1000000000000 : ℝ) (992087938311/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4173/32768 : ℝ)) 2 (496043969217/500000000000 : ℝ) (198417587687/200000000000 : ℝ) (992087938309/1000000000000 : ℝ) (992087938311/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4173/32768 : ℝ)) 3 (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4173/32768 : ℝ)) 4 (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4173/32768 : ℝ)) 5 (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4173/32768 : ℝ)) 6 (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4173/32768 : ℝ)) 7 (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4173/32768 : ℝ))) (88509868573/500000000000 : ℝ) (177019737153/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4173/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88509868573/500000000000 : ℝ) (177019737153/1000000000000 : ℝ) (588509868573/1000000000000 : ℝ) (588509868577/1000000000000 : ℝ) (420737135449/1000000000000 : ℝ) (210368567729/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4173/32768 : ℝ))) 1 (588509868573/1000000000000 : ℝ) (588509868577/1000000000000 : ℝ) (420737135449/1000000000000 : ℝ) (210368567729/500000000000 : ℝ) (504623502011/1000000000000 : ℝ) (252311751009/500000000000 : ℝ) (796163531/1600000000 : ℝ) (497602206883/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4173/32768 : ℝ))) 2 (504623502011/1000000000000 : ℝ) (252311751009/500000000000 : ℝ) (796163531/1600000000 : ℝ) (497602206883/1000000000000 : ℝ) (501112854443/1000000000000 : ℝ) (501112854451/1000000000000 : ℝ) (100220111403/200000000000 : ℝ) (15659392407/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4173/32768 : ℝ))) 3 (501112854443/1000000000000 : ℝ) (501112854451/1000000000000 : ℝ) (100220111403/200000000000 : ℝ) (15659392407/31250000000 : ℝ) (501106705729/1000000000000 : ℝ) (250553352869/500000000000 : ℝ) (501106705691/1000000000000 : ℝ) (5011067057/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4173/32768 : ℝ))) 4 (501106705729/1000000000000 : ℝ) (250553352869/500000000000 : ℝ) (501106705691/1000000000000 : ℝ) (5011067057/10000000000 : ℝ) (50110670571/100000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4173/32768 : ℝ))) 5 (50110670571/100000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4173/32768 : ℝ))) 6 (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4173/32768 : ℝ))) 7 (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4173/32768 : ℝ)) hmem 8 (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4173/32768 : ℝ))) hcmem 8 (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4173/32768 : ℝ)) (992087938371/1000000000000 : ℝ) (992087938373/1000000000000 : ℝ) (501106705709/1000000000000 : ℝ) (501106705719/1000000000000 : ℝ) (31736564561/40000000000 : ℝ) (198353528511/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0695_exp_lower
  have heNumeric : (2054902071913/1000000000000 : ℝ)/4 ≤ Real.exp (-85256469488257/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902071913/1000000000000 : ℝ)/4 ≤ Real.exp ((66767/524288 : ℝ)-(198353528511/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66767/524288 : ℝ) (4173/32768 : ℝ) (198353528511/250000000000 : ℝ) (2054902071913/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0696; no trusted numerical premise.
theorem cover8_leaf0696_exp_radius : (249503026804448339/250000000000000000 : ℝ) ≤ Real.exp ((-66769/4194304 : ℝ)/8) ∧ Real.exp ((-66769/4194304 : ℝ)/8) ≤ (998012107217793357/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66769/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0696_exp_lower : (230028369387494217/250000000000000000 : ℝ) ≤ Real.exp ((-213141174739/320000000000 : ℝ)/8) ∧ Real.exp ((-213141174739/320000000000 : ℝ)/8) ≤ (920113477549976869/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-213141174739/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0696_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451032687/500000000000 : ℝ) ≤ 4*Real.exp (4173/32768 : ℝ)*Real.exp (-mu (radius 8 (66769/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451032687/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66769/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0696_exp_radius
  have hrNumeric : (123025883377/125000000000 : ℝ) ≤ Real.exp (-66769/4194304 : ℝ) ∧ Real.exp (-66769/4194304 : ℝ) ≤ (984207067017/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123025883377/125000000000 : ℝ) ≤ (radius 8 (66769/524288 : ℝ)) ∧ (radius 8 (66769/524288 : ℝ)) ≤ (984207067017/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66769/524288 : ℝ)) (123025883377/125000000000 : ℝ) (984207067017/1000000000000 : ℝ) (88510520891/500000000000 : ℝ) (177021041789/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66769/524288 : ℝ)) (123025883377/125000000000 : ℝ) (984207067017/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66769/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123025883377/125000000000 : ℝ) (984207067017/1000000000000 : ℝ) (248025883377/250000000000 : ℝ) (992103533509/1000000000000 : ℝ) (99207210777/100000000000 : ℝ) (992072107771/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66769/524288 : ℝ)) 1 (248025883377/250000000000 : ℝ) (992103533509/1000000000000 : ℝ) (99207210777/100000000000 : ℝ) (992072107771/1000000000000 : ℝ) (992087820639/1000000000000 : ℝ) (6200548879/6250000000 : ℝ) (496043910257/500000000000 : ℝ) (248021955129/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66769/524288 : ℝ)) 2 (992087820639/1000000000000 : ℝ) (6200548879/6250000000 : ℝ) (496043910257/500000000000 : ℝ) (248021955129/250000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66769/524288 : ℝ)) 3 (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66769/524288 : ℝ)) 4 (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66769/524288 : ℝ)) 5 (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66769/524288 : ℝ)) 6 (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66769/524288 : ℝ)) 7 (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66769/524288 : ℝ))) (88510520891/500000000000 : ℝ) (177021041789/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66769/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88510520891/500000000000 : ℝ) (177021041789/1000000000000 : ℝ) (588510520891/1000000000000 : ℝ) (117702104179/200000000000 : ℝ) (420738685863/1000000000000 : ℝ) (26296167867/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66769/524288 : ℝ))) 1 (588510520891/1000000000000 : ℝ) (117702104179/200000000000 : ℝ) (420738685863/1000000000000 : ℝ) (26296167867/62500000000 : ℝ) (504624603377/1000000000000 : ℝ) (63078075423/125000000000 : ℝ) (248801699741/500000000000 : ℝ) (49760339949/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66769/524288 : ℝ))) 2 (504624603377/1000000000000 : ℝ) (63078075423/125000000000 : ℝ) (248801699741/500000000000 : ℝ) (49760339949/100000000000 : ℝ) (501114001429/1000000000000 : ℝ) (501114001437/1000000000000 : ℝ) (10022034087/20000000000 : ℝ) (250550852179/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66769/524288 : ℝ))) 3 (501114001429/1000000000000 : ℝ) (501114001437/1000000000000 : ℝ) (10022034087/20000000000 : ℝ) (250550852179/500000000000 : ℝ) (501107852889/1000000000000 : ℝ) (250553926449/500000000000 : ℝ) (501107852851/1000000000000 : ℝ) (25055392643/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66769/524288 : ℝ))) 4 (501107852889/1000000000000 : ℝ) (250553926449/500000000000 : ℝ) (501107852851/1000000000000 : ℝ) (25055392643/50000000000 : ℝ) (50110785287/100000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66769/524288 : ℝ))) 5 (50110785287/100000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66769/524288 : ℝ))) 6 (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66769/524288 : ℝ))) 7 (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66769/524288 : ℝ)) hmem 8 (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66769/524288 : ℝ))) hcmem 8 (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66769/524288 : ℝ)) (31002744393/31250000000 : ℝ) (496043910289/500000000000 : ℝ) (501107852869/1000000000000 : ℝ) (501107852879/1000000000000 : ℝ) (793416024557/1000000000000 : ℝ) (31736640983/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0696_exp_lower
  have heNumeric : (1027451032687/500000000000 : ℝ)/4 ≤ Real.exp (-213141174739/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451032687/500000000000 : ℝ)/4 ≤ Real.exp ((4173/32768 : ℝ)-(31736640983/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4173/32768 : ℝ) (66769/524288 : ℝ) (31736640983/40000000000 : ℝ) (1027451032687/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0697; no trusted numerical premise.
theorem cover8_leaf0697_exp_radius : (998012077474715233/1000000000000000000 : ℝ) ≤ Real.exp ((-33385/2097152 : ℝ)/8) ∧ Real.exp ((-33385/2097152 : ℝ)/8) ≤ (499006038737357617/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33385/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0697_exp_lower : (57507092324112483/62500000000000000 : ℝ) ≤ Real.exp ((-17051294060179/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051294060179/25600000000000 : ℝ)/8) ≤ (920113477185799729/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051294060179/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0697_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902058867/1000000000000 : ℝ) ≤ 4*Real.exp (66769/524288 : ℝ)*Real.exp (-mu (radius 8 (33385/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902058867/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33385/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0697_exp_radius
  have hrNumeric : (984206832363/1000000000000 : ℝ) ≤ Real.exp (-33385/2097152 : ℝ) ∧ Real.exp (-33385/2097152 : ℝ) ≤ (246051708091/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984206832363/1000000000000 : ℝ) ≤ (radius 8 (33385/262144 : ℝ)) ∧ (radius 8 (33385/262144 : ℝ)) ≤ (246051708091/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33385/262144 : ℝ)) (984206832363/1000000000000 : ℝ) (246051708091/250000000000 : ℝ) (22127793301/125000000000 : ℝ) (35404469283/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33385/262144 : ℝ)) (984206832363/1000000000000 : ℝ) (246051708091/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33385/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984206832363/1000000000000 : ℝ) (246051708091/250000000000 : ℝ) (992103416181/1000000000000 : ℝ) (496051708091/500000000000 : ℝ) (496035994753/500000000000 : ℝ) (992071989507/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33385/262144 : ℝ)) 1 (992103416181/1000000000000 : ℝ) (496051708091/500000000000 : ℝ) (496035994753/500000000000 : ℝ) (992071989507/1000000000000 : ℝ) (992087702843/1000000000000 : ℝ) (198417540569/200000000000 : ℝ) (992087702719/1000000000000 : ℝ) (992087702721/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33385/262144 : ℝ)) 2 (992087702843/1000000000000 : ℝ) (198417540569/200000000000 : ℝ) (992087702719/1000000000000 : ℝ) (992087702721/1000000000000 : ℝ) (992087702781/1000000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33385/262144 : ℝ)) 3 (992087702781/1000000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33385/262144 : ℝ)) 4 (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33385/262144 : ℝ)) 5 (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33385/262144 : ℝ)) 6 (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33385/262144 : ℝ)) 7 (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33385/262144 : ℝ))) (22127793301/125000000000 : ℝ) (35404469283/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33385/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22127793301/125000000000 : ℝ) (35404469283/200000000000 : ℝ) (147127793301/250000000000 : ℝ) (73563896651/125000000000 : ℝ) (420740236259/1000000000000 : ℝ) (420740236269/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33385/262144 : ℝ))) 1 (147127793301/250000000000 : ℝ) (73563896651/125000000000 : ℝ) (420740236259/1000000000000 : ℝ) (420740236269/1000000000000 : ℝ) (504625704731/1000000000000 : ℝ) (504625704739/1000000000000 : ℝ) (19904183683/40000000000 : ℝ) (124401148021/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33385/262144 : ℝ))) 2 (504625704731/1000000000000 : ℝ) (504625704739/1000000000000 : ℝ) (19904183683/40000000000 : ℝ) (124401148021/250000000000 : ℝ) (501115148403/1000000000000 : ℝ) (125278787103/250000000000 : ℝ) (501102851671/1000000000000 : ℝ) (3131892823/6250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33385/262144 : ℝ))) 3 (501115148403/1000000000000 : ℝ) (125278787103/250000000000 : ℝ) (501102851671/1000000000000 : ℝ) (3131892823/6250000000 : ℝ) (501109000037/1000000000000 : ℝ) (250554500023/500000000000 : ℝ) (501108999999/1000000000000 : ℝ) (501109000009/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33385/262144 : ℝ))) 4 (501109000037/1000000000000 : ℝ) (250554500023/500000000000 : ℝ) (501108999999/1000000000000 : ℝ) (501109000009/1000000000000 : ℝ) (250554500009/500000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33385/262144 : ℝ))) 5 (250554500009/500000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33385/262144 : ℝ))) 6 (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33385/262144 : ℝ))) 7 (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33385/262144 : ℝ)) hmem 8 (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33385/262144 : ℝ))) hcmem 8 (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33385/262144 : ℝ)) (49604385139/50000000000 : ℝ) (992087702783/1000000000000 : ℝ) (501109000017/1000000000000 : ℝ) (125277250007/250000000000 : ℝ) (79341793507/100000000000 : ℝ) (79341793509/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0697_exp_lower
  have heNumeric : (2054902058867/1000000000000 : ℝ)/4 ≤ Real.exp (-17051294060179/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902058867/1000000000000 : ℝ)/4 ≤ Real.exp ((66769/524288 : ℝ)-(79341793509/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66769/524288 : ℝ) (33385/262144 : ℝ) (79341793509/100000000000 : ℝ) (2054902058867/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0698; no trusted numerical premise.
theorem cover8_leaf0698_exp_radius : (998012047731637997/1000000000000000000 : ℝ) ≤ Real.exp ((-66771/4194304 : ℝ)/8) ∧ Real.exp ((-66771/4194304 : ℝ)/8) ≤ (499006023865818999/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66771/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0698_exp_lower : (920113476823922871/1000000000000000000 : ℝ) ≤ Real.exp ((-8525647070363/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525647070363/12800000000000 : ℝ)/8) ≤ (115014184602990359/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525647070363/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0698_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451026201/500000000000 : ℝ) ≤ 4*Real.exp (33385/262144 : ℝ)*Real.exp (-mu (radius 8 (66771/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451026201/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66771/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0698_exp_radius
  have hrNumeric : (98420659771/100000000000 : ℝ) ≤ Real.exp (-66771/4194304 : ℝ) ∧ Real.exp (-66771/4194304 : ℝ) ≤ (984206597711/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98420659771/100000000000 : ℝ) ≤ (radius 8 (66771/524288 : ℝ)) ∧ (radius 8 (66771/524288 : ℝ)) ≤ (984206597711/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66771/524288 : ℝ)) (98420659771/100000000000 : ℝ) (984206597711/1000000000000 : ℝ) (11063978189/62500000000 : ℝ) (177023651031/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66771/524288 : ℝ)) (98420659771/100000000000 : ℝ) (984206597711/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66771/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98420659771/100000000000 : ℝ) (984206597711/1000000000000 : ℝ) (198420659771/200000000000 : ℝ) (124012912357/125000000000 : ℝ) (496035935621/500000000000 : ℝ) (992071871243/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66771/524288 : ℝ)) 1 (198420659771/200000000000 : ℝ) (124012912357/125000000000 : ℝ) (496035935621/500000000000 : ℝ) (992071871243/1000000000000 : ℝ) (124010948131/125000000000 : ℝ) (19841751701/20000000000 : ℝ) (248021896231/250000000000 : ℝ) (496043792463/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66771/524288 : ℝ)) 2 (124010948131/125000000000 : ℝ) (19841751701/20000000000 : ℝ) (248021896231/250000000000 : ℝ) (496043792463/500000000000 : ℝ) (496043792493/500000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66771/524288 : ℝ)) 3 (496043792493/500000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66771/524288 : ℝ)) 4 (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66771/524288 : ℝ)) 5 (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66771/524288 : ℝ)) 6 (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66771/524288 : ℝ)) 7 (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66771/524288 : ℝ))) (11063978189/62500000000 : ℝ) (177023651031/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66771/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11063978189/62500000000 : ℝ) (177023651031/1000000000000 : ℝ) (73563978189/125000000000 : ℝ) (147127956379/250000000000 : ℝ) (210370893319/500000000000 : ℝ) (52592723331/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66771/524288 : ℝ))) 1 (73563978189/125000000000 : ℝ) (147127956379/250000000000 : ℝ) (210370893319/500000000000 : ℝ) (52592723331/125000000000 : ℝ) (20185072243/40000000000 : ℝ) (252313403041/500000000000 : ℝ) (31100361541/62500000000 : ℝ) (99521156933/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66771/524288 : ℝ))) 2 (20185072243/40000000000 : ℝ) (252313403041/500000000000 : ℝ) (31100361541/62500000000 : ℝ) (99521156933/200000000000 : ℝ) (100223259073/200000000000 : ℝ) (250558147687/500000000000 : ℝ) (501103998981/1000000000000 : ℝ) (50110399899/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66771/524288 : ℝ))) 3 (100223259073/200000000000 : ℝ) (250558147687/500000000000 : ℝ) (501103998981/1000000000000 : ℝ) (50110399899/100000000000 : ℝ) (501110147173/1000000000000 : ℝ) (250555073591/500000000000 : ℝ) (100222029427/200000000000 : ℝ) (100222029429/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66771/524288 : ℝ))) 4 (501110147173/1000000000000 : ℝ) (250555073591/500000000000 : ℝ) (100222029427/200000000000 : ℝ) (100222029429/200000000000 : ℝ) (250555073577/500000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66771/524288 : ℝ))) 5 (250555073577/500000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66771/524288 : ℝ))) 6 (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66771/524288 : ℝ))) 7 (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66771/524288 : ℝ)) hmem 8 (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66771/524288 : ℝ))) hcmem 8 (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66771/524288 : ℝ)) (198417516997/200000000000 : ℝ) (248021896247/250000000000 : ℝ) (501110147153/1000000000000 : ℝ) (125277536791/250000000000 : ℝ) (198354961391/250000000000 : ℝ) (158683969117/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0698_exp_lower
  have heNumeric : (1027451026201/500000000000 : ℝ)/4 ≤ Real.exp (-8525647070363/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451026201/500000000000 : ℝ)/4 ≤ Real.exp ((33385/262144 : ℝ)-(158683969117/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33385/262144 : ℝ) (66771/524288 : ℝ) (158683969117/200000000000 : ℝ) (1027451026201/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0699; no trusted numerical premise.
theorem cover8_leaf0699_exp_radius : (998012017988561647/1000000000000000000 : ℝ) ≤ Real.exp ((-16693/1048576 : ℝ)/8) ∧ Real.exp ((-16693/1048576 : ℝ)/8) ≤ (62375751124285103/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16693/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0699_exp_lower : (920113476464461313/1000000000000000000 : ℝ) ≤ Real.exp ((-85256471103677/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256471103677/128000000000000 : ℝ)/8) ≤ (460056738232230657/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256471103677/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0699_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745102299/50000000000 : ℝ) ≤ 4*Real.exp (66771/524288 : ℝ)*Real.exp (-mu (radius 8 (16693/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (102745102299/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16693/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0699_exp_radius
  have hrNumeric : (984206363057/1000000000000 : ℝ) ≤ Real.exp (-16693/1048576 : ℝ) ∧ Real.exp (-16693/1048576 : ℝ) ≤ (492103181529/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984206363057/1000000000000 : ℝ) ≤ (radius 8 (16693/131072 : ℝ)) ∧ (radius 8 (16693/131072 : ℝ)) ≤ (492103181529/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16693/131072 : ℝ)) (984206363057/1000000000000 : ℝ) (492103181529/500000000000 : ℝ) (17702495563/100000000000 : ℝ) (177024955637/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16693/131072 : ℝ)) (984206363057/1000000000000 : ℝ) (492103181529/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16693/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984206363057/1000000000000 : ℝ) (492103181529/500000000000 : ℝ) (124012897691/125000000000 : ℝ) (992103181529/1000000000000 : ℝ) (496035876489/500000000000 : ℝ) (992071752979/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16693/131072 : ℝ)) 1 (124012897691/125000000000 : ℝ) (992103181529/1000000000000 : ℝ) (496035876489/500000000000 : ℝ) (992071752979/1000000000000 : ℝ) (992087467253/1000000000000 : ℝ) (496043733627/500000000000 : ℝ) (124010933391/125000000000 : ℝ) (99208746713/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16693/131072 : ℝ)) 2 (992087467253/1000000000000 : ℝ) (496043733627/500000000000 : ℝ) (124010933391/125000000000 : ℝ) (99208746713/100000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16693/131072 : ℝ)) 3 (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16693/131072 : ℝ)) 4 (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16693/131072 : ℝ)) 5 (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16693/131072 : ℝ)) 6 (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16693/131072 : ℝ)) 7 (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16693/131072 : ℝ))) (17702495563/100000000000 : ℝ) (177024955637/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16693/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17702495563/100000000000 : ℝ) (177024955637/1000000000000 : ℝ) (117702495563/200000000000 : ℝ) (588512477819/1000000000000 : ℝ) (420743337/1000000000 : ℝ) (420743337009/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16693/131072 : ℝ))) 1 (117702495563/200000000000 : ℝ) (588512477819/1000000000000 : ℝ) (420743337/1000000000 : ℝ) (420743337009/1000000000000 : ℝ) (504627907407/1000000000000 : ℝ) (252313953707/500000000000 : ℝ) (62200872153/125000000000 : ℝ) (31100436077/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16693/131072 : ℝ))) 2 (504627907407/1000000000000 : ℝ) (252313953707/500000000000 : ℝ) (62200872153/125000000000 : ℝ) (31100436077/62500000000 : ℝ) (100223488463/200000000000 : ℝ) (501117442323/1000000000000 : ℝ) (501105146279/1000000000000 : ℝ) (501105146287/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16693/131072 : ℝ))) 3 (100223488463/200000000000 : ℝ) (501117442323/1000000000000 : ℝ) (501105146279/1000000000000 : ℝ) (501105146287/1000000000000 : ℝ) (501111294297/1000000000000 : ℝ) (100222258861/200000000000 : ℝ) (501111294259/1000000000000 : ℝ) (125277823567/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16693/131072 : ℝ))) 4 (501111294297/1000000000000 : ℝ) (100222258861/200000000000 : ℝ) (501111294259/1000000000000 : ℝ) (125277823567/250000000000 : ℝ) (250555647139/500000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16693/131072 : ℝ))) 5 (250555647139/500000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16693/131072 : ℝ))) 6 (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16693/131072 : ℝ))) 7 (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16693/131072 : ℝ)) hmem 8 (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16693/131072 : ℝ))) hcmem 8 (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16693/131072 : ℝ)) (99208746719/100000000000 : ℝ) (124010933399/125000000000 : ℝ) (501111294277/1000000000000 : ℝ) (501111294287/1000000000000 : ℝ) (793421756041/1000000000000 : ℝ) (793421756059/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0699_exp_lower
  have heNumeric : (102745102299/50000000000 : ℝ)/4 ≤ Real.exp (-85256471103677/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745102299/50000000000 : ℝ)/4 ≤ Real.exp ((66771/524288 : ℝ)-(793421756059/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66771/524288 : ℝ) (16693/131072 : ℝ) (793421756059/1000000000000 : ℝ) (102745102299/50000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0675_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0675_certificate
#check SmaleRate.Proofs.cover8_leaf0676_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0676_certificate
#check SmaleRate.Proofs.cover8_leaf0677_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0677_certificate
#check SmaleRate.Proofs.cover8_leaf0678_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0678_certificate
#check SmaleRate.Proofs.cover8_leaf0679_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0679_certificate
#check SmaleRate.Proofs.cover8_leaf0680_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0680_certificate
#check SmaleRate.Proofs.cover8_leaf0681_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0681_certificate
#check SmaleRate.Proofs.cover8_leaf0682_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0682_certificate
#check SmaleRate.Proofs.cover8_leaf0683_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0683_certificate
#check SmaleRate.Proofs.cover8_leaf0684_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0684_certificate
#check SmaleRate.Proofs.cover8_leaf0685_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0685_certificate
#check SmaleRate.Proofs.cover8_leaf0686_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0686_certificate
#check SmaleRate.Proofs.cover8_leaf0687_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0687_certificate
#check SmaleRate.Proofs.cover8_leaf0688_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0688_certificate
#check SmaleRate.Proofs.cover8_leaf0689_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0689_certificate
#check SmaleRate.Proofs.cover8_leaf0690_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0690_certificate
#check SmaleRate.Proofs.cover8_leaf0691_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0691_certificate
#check SmaleRate.Proofs.cover8_leaf0692_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0692_certificate
#check SmaleRate.Proofs.cover8_leaf0693_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0693_certificate
#check SmaleRate.Proofs.cover8_leaf0694_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0694_certificate
#check SmaleRate.Proofs.cover8_leaf0695_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0695_certificate
#check SmaleRate.Proofs.cover8_leaf0696_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0696_certificate
#check SmaleRate.Proofs.cover8_leaf0697_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0697_certificate
#check SmaleRate.Proofs.cover8_leaf0698_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0698_certificate
#check SmaleRate.Proofs.cover8_leaf0699_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0699_certificate
