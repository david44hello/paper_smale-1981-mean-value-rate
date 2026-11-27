/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0875; no trusted numerical premise.
theorem cover8_leaf0875_exp_radius : (998006783220930771/1000000000000000000 : ℝ) ≤ Real.exp ((-16737/1048576 : ℝ)/8) ∧ Real.exp ((-16737/1048576 : ℝ)/8) ≤ (249501695805232693/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16737/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0875_exp_lower : (460056723935874289/500000000000000000 : ℝ) ≤ Real.exp ((-17051300584937/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051300584937/25600000000000 : ℝ)/8) ≤ (920113447871748579/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051300584937/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0875_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862691891/125000000000 : ℝ) ≤ 4*Real.exp (66947/524288 : ℝ)*Real.exp (-mu (radius 8 (16737/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862691891/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16737/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0875_exp_radius
  have hrNumeric : (984165064981/1000000000000 : ℝ) ≤ Real.exp (-16737/1048576 : ℝ) ∧ Real.exp (-16737/1048576 : ℝ) ≤ (492082532491/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984165064981/1000000000000 : ℝ) ≤ (radius 8 (16737/131072 : ℝ)) ∧ (radius 8 (16737/131072 : ℝ)) ≤ (492082532491/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16737/131072 : ℝ)) (984165064981/1000000000000 : ℝ) (492082532491/500000000000 : ℝ) (177254407191/1000000000000 : ℝ) (88627203599/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16737/131072 : ℝ)) (984165064981/1000000000000 : ℝ) (492082532491/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16737/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984165064981/1000000000000 : ℝ) (492082532491/500000000000 : ℝ) (99208253249/100000000000 : ℝ) (992082532491/1000000000000 : ℝ) (496025469351/500000000000 : ℝ) (62003183669/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16737/131072 : ℝ)) 1 (99208253249/100000000000 : ℝ) (992082532491/1000000000000 : ℝ) (496025469351/500000000000 : ℝ) (62003183669/62500000000 : ℝ) (248016683899/250000000000 : ℝ) (496033367799/500000000000 : ℝ) (99206673547/100000000000 : ℝ) (62004170967/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16737/131072 : ℝ)) 2 (248016683899/250000000000 : ℝ) (496033367799/500000000000 : ℝ) (99206673547/100000000000 : ℝ) (62004170967/62500000000 : ℝ) (992066735533/1000000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16737/131072 : ℝ)) 3 (992066735533/1000000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16737/131072 : ℝ)) 4 (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16737/131072 : ℝ)) 5 (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16737/131072 : ℝ)) 6 (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16737/131072 : ℝ)) 7 (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16737/131072 : ℝ))) (177254407191/1000000000000 : ℝ) (88627203599/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16737/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177254407191/1000000000000 : ℝ) (88627203599/500000000000 : ℝ) (117725440719/200000000000 : ℝ) (588627203599/1000000000000 : ℝ) (52626990341/125000000000 : ℝ) (421015922737/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16737/131072 : ℝ))) 1 (117725440719/200000000000 : ℝ) (588627203599/1000000000000 : ℝ) (52626990341/125000000000 : ℝ) (421015922737/1000000000000 : ℝ) (504821563161/1000000000000 : ℝ) (15775673849/31250000000 : ℝ) (497816658283/1000000000000 : ℝ) (497816658291/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16737/131072 : ℝ))) 2 (504821563161/1000000000000 : ℝ) (15775673849/31250000000 : ℝ) (497816658283/1000000000000 : ℝ) (497816658291/1000000000000 : ℝ) (250659555361/500000000000 : ℝ) (50131911073/100000000000 : ℝ) (501306875677/1000000000000 : ℝ) (250653437843/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16737/131072 : ℝ))) 3 (250659555361/500000000000 : ℝ) (50131911073/100000000000 : ℝ) (501306875677/1000000000000 : ℝ) (250653437843/500000000000 : ℝ) (501312993199/1000000000000 : ℝ) (62664124151/125000000000 : ℝ) (250656496581/500000000000 : ℝ) (501312993171/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16737/131072 : ℝ))) 4 (501312993199/1000000000000 : ℝ) (62664124151/125000000000 : ℝ) (250656496581/500000000000 : ℝ) (501312993171/1000000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16737/131072 : ℝ))) 5 (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16737/131072 : ℝ))) 6 (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16737/131072 : ℝ))) 7 (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16737/131072 : ℝ)) hmem 8 (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16737/131072 : ℝ))) hcmem 8 (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16737/131072 : ℝ)) (248016683883/250000000000 : ℝ) (198413347107/200000000000 : ℝ) (25065649659/50000000000 : ℝ) (50131299319/100000000000 : ℝ) (793757698001/1000000000000 : ℝ) (39687884901/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0875_exp_lower
  have heNumeric : (256862691891/125000000000 : ℝ)/4 ≤ Real.exp (-17051300584937/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862691891/125000000000 : ℝ)/4 ≤ Real.exp ((66947/524288 : ℝ)-(39687884901/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66947/524288 : ℝ) (16737/131072 : ℝ) (39687884901/50000000000 : ℝ) (256862691891/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0876; no trusted numerical premise.
theorem cover8_leaf0876_exp_radius : (199601350695602263/200000000000000000 : ℝ) ≤ Real.exp ((-66949/4194304 : ℝ)/8) ∧ Real.exp ((-66949/4194304 : ℝ)/8) ≤ (249501688369502829/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66949/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0876_exp_lower : (920113447905405501/1000000000000000000 : ℝ) ≤ Real.exp ((-21314125721807/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125721807/32000000000000 : ℝ)/8) ≤ (460056723952702751/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125721807/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0876_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901535729/1000000000000 : ℝ) ≤ 4*Real.exp (16737/131072 : ℝ)*Real.exp (-mu (radius 8 (66949/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901535729/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66949/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0876_exp_radius
  have hrNumeric : (984164830337/1000000000000 : ℝ) ≤ Real.exp (-66949/4194304 : ℝ) ∧ Real.exp (-66949/4194304 : ℝ) ≤ (492082415169/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984164830337/1000000000000 : ℝ) ≤ (radius 8 (66949/524288 : ℝ)) ∧ (radius 8 (66949/524288 : ℝ)) ≤ (492082415169/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66949/524288 : ℝ)) (984164830337/1000000000000 : ℝ) (492082415169/500000000000 : ℝ) (88627854997/500000000000 : ℝ) (177255710001/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66949/524288 : ℝ)) (984164830337/1000000000000 : ℝ) (492082415169/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66949/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984164830337/1000000000000 : ℝ) (492082415169/500000000000 : ℝ) (15501287737/15625000000 : ℝ) (992082415169/1000000000000 : ℝ) (24801270511/25000000000 : ℝ) (496025410221/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66949/524288 : ℝ)) 1 (15501287737/15625000000 : ℝ) (992082415169/1000000000000 : ℝ) (24801270511/25000000000 : ℝ) (496025410221/500000000000 : ℝ) (248016654451/250000000000 : ℝ) (496033308903/500000000000 : ℝ) (496033308839/500000000000 : ℝ) (12400832721/12500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66949/524288 : ℝ)) 2 (248016654451/250000000000 : ℝ) (496033308903/500000000000 : ℝ) (496033308839/500000000000 : ℝ) (12400832721/12500000000 : ℝ) (992066617741/1000000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66949/524288 : ℝ)) 3 (992066617741/1000000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66949/524288 : ℝ)) 4 (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66949/524288 : ℝ)) 5 (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66949/524288 : ℝ)) 6 (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66949/524288 : ℝ)) 7 (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66949/524288 : ℝ))) (88627854997/500000000000 : ℝ) (177255710001/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66949/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88627854997/500000000000 : ℝ) (177255710001/1000000000000 : ℝ) (588627854997/1000000000000 : ℝ) (588627855001/1000000000000 : ℝ) (421017469939/1000000000000 : ℝ) (105254367487/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66949/524288 : ℝ))) 1 (588627854997/1000000000000 : ℝ) (588627855001/1000000000000 : ℝ) (421017469939/1000000000000 : ℝ) (105254367487/250000000000 : ℝ) (126205665617/250000000000 : ℝ) (20192906499/40000000000 : ℝ) (497817848461/1000000000000 : ℝ) (497817848469/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66949/524288 : ℝ))) 2 (126205665617/250000000000 : ℝ) (20192906499/40000000000 : ℝ) (497817848461/1000000000000 : ℝ) (497817848469/1000000000000 : ℝ) (62665031933/125000000000 : ℝ) (31332515967/62500000000 : ℝ) (100261604153/200000000000 : ℝ) (250654010387/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66949/524288 : ℝ))) 3 (62665031933/125000000000 : ℝ) (31332515967/62500000000 : ℝ) (100261604153/200000000000 : ℝ) (250654010387/500000000000 : ℝ) (250657069057/500000000000 : ℝ) (501314138123/1000000000000 : ℝ) (501314138077/1000000000000 : ℝ) (250657069043/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66949/524288 : ℝ))) 4 (250657069057/500000000000 : ℝ) (501314138123/1000000000000 : ℝ) (501314138077/1000000000000 : ℝ) (250657069043/500000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66949/524288 : ℝ))) 5 (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66949/524288 : ℝ))) 6 (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66949/524288 : ℝ))) 7 (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66949/524288 : ℝ)) hmem 8 (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66949/524288 : ℝ))) hcmem 8 (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66949/524288 : ℝ)) (49603330887/50000000000 : ℝ) (992066617743/1000000000000 : ℝ) (100262827619/200000000000 : ℝ) (100262827621/200000000000 : ℝ) (793759605057/1000000000000 : ℝ) (198439901269/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0876_exp_lower
  have heNumeric : (2054901535729/1000000000000 : ℝ)/4 ≤ Real.exp (-21314125721807/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901535729/1000000000000 : ℝ)/4 ≤ Real.exp ((16737/131072 : ℝ)-(198439901269/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16737/131072 : ℝ) (66949/524288 : ℝ) (198439901269/250000000000 : ℝ) (2054901535729/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0877; no trusted numerical premise.
theorem cover8_leaf0877_exp_radius : (499003361867546373/500000000000000000 : ℝ) ≤ Real.exp ((-33475/2097152 : ℝ)/8) ∧ Real.exp ((-33475/2097152 : ℝ)/8) ≤ (998006723735092747/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33475/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0877_exp_lower : (184022689588479567/200000000000000000 : ℝ) ≤ Real.exp ((-85256502846059/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502846059/128000000000000 : ℝ)/8) ≤ (230028361985599459/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502846059/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0877_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490153639/100000000000 : ℝ) ≤ 4*Real.exp (66949/524288 : ℝ)*Real.exp (-mu (radius 8 (33475/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490153639/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33475/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0877_exp_radius
  have hrNumeric : (492082297847/500000000000 : ℝ) ≤ Real.exp (-33475/2097152 : ℝ) ∧ Real.exp (-33475/2097152 : ℝ) ≤ (196832919139/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492082297847/500000000000 : ℝ) ≤ (radius 8 (33475/262144 : ℝ)) ∧ (radius 8 (33475/262144 : ℝ)) ≤ (196832919139/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33475/262144 : ℝ)) (492082297847/500000000000 : ℝ) (196832919139/200000000000 : ℝ) (88628506391/500000000000 : ℝ) (44314253197/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33475/262144 : ℝ)) (492082297847/500000000000 : ℝ) (196832919139/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33475/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492082297847/500000000000 : ℝ) (196832919139/200000000000 : ℝ) (992082297847/1000000000000 : ℝ) (124010287231/125000000000 : ℝ) (992050702179/1000000000000 : ℝ) (49602535109/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33475/262144 : ℝ)) 1 (992082297847/1000000000000 : ℝ) (124010287231/125000000000 : ℝ) (992050702179/1000000000000 : ℝ) (49602535109/50000000000 : ℝ) (992066500013/1000000000000 : ℝ) (496033250007/500000000000 : ℝ) (992066499887/1000000000000 : ℝ) (992066499889/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33475/262144 : ℝ)) 2 (992066500013/1000000000000 : ℝ) (496033250007/500000000000 : ℝ) (992066499887/1000000000000 : ℝ) (992066499889/1000000000000 : ℝ) (19841329999/20000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33475/262144 : ℝ)) 3 (19841329999/20000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33475/262144 : ℝ)) 4 (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33475/262144 : ℝ)) 5 (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33475/262144 : ℝ)) 6 (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33475/262144 : ℝ)) 7 (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33475/262144 : ℝ))) (88628506391/500000000000 : ℝ) (44314253197/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33475/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88628506391/500000000000 : ℝ) (44314253197/250000000000 : ℝ) (588628506391/1000000000000 : ℝ) (294314253197/500000000000 : ℝ) (210509508563/500000000000 : ℝ) (210509508567/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33475/262144 : ℝ))) 1 (588628506391/1000000000000 : ℝ) (294314253197/500000000000 : ℝ) (210509508563/500000000000 : ℝ) (210509508567/500000000000 : ℝ) (252411880879/500000000000 : ℝ) (126205940441/250000000000 : ℝ) (24890951931/50000000000 : ℝ) (497819038627/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33475/262144 : ℝ))) 2 (252411880879/500000000000 : ℝ) (126205940441/250000000000 : ℝ) (24890951931/50000000000 : ℝ) (497819038627/1000000000000 : ℝ) (501321400189/1000000000000 : ℝ) (125330350049/250000000000 : ℝ) (100261833167/200000000000 : ℝ) (501309165843/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33475/262144 : ℝ))) 3 (501321400189/1000000000000 : ℝ) (125330350049/250000000000 : ℝ) (100261833167/200000000000 : ℝ) (501309165843/1000000000000 : ℝ) (125328820753/250000000000 : ℝ) (25065764151/50000000000 : ℝ) (250657641487/500000000000 : ℝ) (501315282983/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33475/262144 : ℝ))) 4 (125328820753/250000000000 : ℝ) (25065764151/50000000000 : ℝ) (250657641487/500000000000 : ℝ) (501315282983/1000000000000 : ℝ) (501315282993/1000000000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33475/262144 : ℝ))) 5 (501315282993/1000000000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33475/262144 : ℝ))) 6 (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33475/262144 : ℝ))) 7 (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33475/262144 : ℝ)) hmem 8 (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33475/262144 : ℝ))) hcmem 8 (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33475/262144 : ℝ)) (992066499949/1000000000000 : ℝ) (62004156247/62500000000 : ℝ) (31332205187/62500000000 : ℝ) (250657641501/500000000000 : ℝ) (198440378021/250000000000 : ℝ) (793761512103/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0877_exp_lower
  have heNumeric : (205490153639/100000000000 : ℝ)/4 ≤ Real.exp (-85256502846059/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490153639/100000000000 : ℝ)/4 ≤ Real.exp ((66949/524288 : ℝ)-(793761512103/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66949/524288 : ℝ) (33475/262144 : ℝ) (793761512103/1000000000000 : ℝ) (205490153639/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0878; no trusted numerical premise.
theorem cover8_leaf0878_exp_radius : (124750836749021883/125000000000000000 : ℝ) ≤ Real.exp ((-66951/4194304 : ℝ)/8) ∧ Real.exp ((-66951/4194304 : ℝ)/8) ≤ (199601338798435013/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66951/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0878_exp_lower : (36804537919258417/40000000000000000 : ℝ) ≤ Real.exp ((-42628251401293/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251401293/64000000000000 : ℝ)/8) ≤ (460056723990730213/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251401293/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0878_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (32107836517/15625000000 : ℝ) ≤ 4*Real.exp (33475/262144 : ℝ)*Real.exp (-mu (radius 8 (66951/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (32107836517/15625000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66951/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0878_exp_radius
  have hrNumeric : (984164361051/1000000000000 : ℝ) ≤ Real.exp (-66951/4194304 : ℝ) ∧ Real.exp (-66951/4194304 : ℝ) ≤ (246041090263/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984164361051/1000000000000 : ℝ) ≤ (radius 8 (66951/524288 : ℝ)) ∧ (radius 8 (66951/524288 : ℝ)) ≤ (246041090263/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66951/524288 : ℝ)) (984164361051/1000000000000 : ℝ) (246041090263/250000000000 : ℝ) (177258315559/1000000000000 : ℝ) (88629157783/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66951/524288 : ℝ)) (984164361051/1000000000000 : ℝ) (246041090263/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66951/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984164361051/1000000000000 : ℝ) (246041090263/250000000000 : ℝ) (39683287221/40000000000 : ℝ) (496041090263/500000000000 : ℝ) (992050583917/1000000000000 : ℝ) (496025291959/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66951/524288 : ℝ)) 1 (39683287221/40000000000 : ℝ) (496041090263/500000000000 : ℝ) (992050583917/1000000000000 : ℝ) (496025291959/500000000000 : ℝ) (992066382221/1000000000000 : ℝ) (496033191111/500000000000 : ℝ) (198413276419/200000000000 : ℝ) (992066382097/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66951/524288 : ℝ)) 2 (992066382221/1000000000000 : ℝ) (496033191111/500000000000 : ℝ) (198413276419/200000000000 : ℝ) (992066382097/1000000000000 : ℝ) (496033191079/500000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66951/524288 : ℝ)) 3 (496033191079/500000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66951/524288 : ℝ)) 4 (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66951/524288 : ℝ)) 5 (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66951/524288 : ℝ)) 6 (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66951/524288 : ℝ)) 7 (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66951/524288 : ℝ))) (177258315559/1000000000000 : ℝ) (88629157783/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66951/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177258315559/1000000000000 : ℝ) (88629157783/500000000000 : ℝ) (588629157779/1000000000000 : ℝ) (588629157783/1000000000000 : ℝ) (210510282147/500000000000 : ℝ) (421020564303/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66951/524288 : ℝ))) 1 (588629157779/1000000000000 : ℝ) (588629157783/1000000000000 : ℝ) (210510282147/500000000000 : ℝ) (421020564303/1000000000000 : ℝ) (126206215259/250000000000 : ℝ) (504824861043/1000000000000 : ℝ) (99564045753/200000000000 : ℝ) (497820228773/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66951/524288 : ℝ))) 2 (126206215259/250000000000 : ℝ) (504824861043/1000000000000 : ℝ) (99564045753/200000000000 : ℝ) (497820228773/1000000000000 : ℝ) (5013225449/10000000000 : ℝ) (125330636227/250000000000 : ℝ) (125327577723/250000000000 : ℝ) (501310310901/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66951/524288 : ℝ))) 3 (5013225449/10000000000 : ℝ) (125330636227/250000000000 : ℝ) (125327577723/250000000000 : ℝ) (501310310901/1000000000000 : ℝ) (62664553487/125000000000 : ℝ) (100263285581/200000000000 : ℝ) (250658213929/500000000000 : ℝ) (125329106967/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66951/524288 : ℝ))) 4 (62664553487/125000000000 : ℝ) (100263285581/200000000000 : ℝ) (250658213929/500000000000 : ℝ) (125329106967/250000000000 : ℝ) (501316427877/1000000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66951/524288 : ℝ))) 5 (501316427877/1000000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66951/524288 : ℝ))) 6 (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66951/524288 : ℝ))) 7 (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66951/524288 : ℝ)) hmem 8 (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66951/524288 : ℝ))) hcmem 8 (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66951/524288 : ℝ)) (992066382157/1000000000000 : ℝ) (12400829777/12500000000 : ℝ) (125329106969/250000000000 : ℝ) (501316427887/1000000000000 : ℝ) (198440854773/250000000000 : ℝ) (99220427389/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0878_exp_lower
  have heNumeric : (32107836517/15625000000 : ℝ)/4 ≤ Real.exp (-42628251401293/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (32107836517/15625000000 : ℝ)/4 ≤ Real.exp ((33475/262144 : ℝ)-(99220427389/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33475/262144 : ℝ) (66951/524288 : ℝ) (99220427389/125000000000 : ℝ) (32107836517/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0879; no trusted numerical premise.
theorem cover8_leaf0879_exp_radius : (998006664249258267/1000000000000000000 : ℝ) ≤ Real.exp ((-8369/524288 : ℝ)/8) ∧ Real.exp ((-8369/524288 : ℝ)/8) ≤ (249501666062314567/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8369/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0879_exp_lower : (92011344802259327/100000000000000000 : ℝ) ≤ Real.exp ((-85256502756809/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502756809/128000000000000 : ℝ)/8) ≤ (920113448022593271/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502756809/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0879_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901537823/1000000000000 : ℝ) ≤ 4*Real.exp (66951/524288 : ℝ)*Real.exp (-mu (radius 8 (8369/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901537823/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8369/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0879_exp_radius
  have hrNumeric : (123020515801/125000000000 : ℝ) ≤ Real.exp (-8369/524288 : ℝ) ∧ Real.exp (-8369/524288 : ℝ) ≤ (984164126409/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123020515801/125000000000 : ℝ) ≤ (radius 8 (8369/65536 : ℝ)) ∧ (radius 8 (8369/65536 : ℝ)) ≤ (984164126409/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8369/65536 : ℝ)) (123020515801/125000000000 : ℝ) (984164126409/1000000000000 : ℝ) (177259618327/1000000000000 : ℝ) (88629809167/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8369/65536 : ℝ)) (123020515801/125000000000 : ℝ) (984164126409/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8369/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123020515801/125000000000 : ℝ) (984164126409/1000000000000 : ℝ) (248020515801/250000000000 : ℝ) (198416412641/200000000000 : ℝ) (198410093131/200000000000 : ℝ) (992050465657/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8369/65536 : ℝ)) 1 (248020515801/250000000000 : ℝ) (198416412641/200000000000 : ℝ) (198410093131/200000000000 : ℝ) (992050465657/1000000000000 : ℝ) (992066264429/1000000000000 : ℝ) (992066264431/1000000000000 : ℝ) (992066264303/1000000000000 : ℝ) (496033132153/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8369/65536 : ℝ)) 2 (992066264429/1000000000000 : ℝ) (992066264431/1000000000000 : ℝ) (992066264303/1000000000000 : ℝ) (496033132153/500000000000 : ℝ) (496033132183/500000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8369/65536 : ℝ)) 3 (496033132183/500000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8369/65536 : ℝ)) 4 (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8369/65536 : ℝ)) 5 (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8369/65536 : ℝ)) 6 (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8369/65536 : ℝ)) 7 (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8369/65536 : ℝ))) (177259618327/1000000000000 : ℝ) (88629809167/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8369/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177259618327/1000000000000 : ℝ) (88629809167/500000000000 : ℝ) (588629809163/1000000000000 : ℝ) (588629809167/1000000000000 : ℝ) (210511055723/500000000000 : ℝ) (84204422291/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8369/65536 : ℝ))) 1 (588629809163/1000000000000 : ℝ) (588629809167/1000000000000 : ℝ) (210511055723/500000000000 : ℝ) (84204422291/200000000000 : ℝ) (31551622519/62500000000 : ℝ) (504825960311/1000000000000 : ℝ) (248910709449/500000000000 : ℝ) (248910709453/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8369/65536 : ℝ))) 2 (31551622519/62500000000 : ℝ) (504825960311/1000000000000 : ℝ) (248910709449/500000000000 : ℝ) (248910709453/500000000000 : ℝ) (501323689601/1000000000000 : ℝ) (501323689609/1000000000000 : ℝ) (250655727969/500000000000 : ℝ) (250655727973/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8369/65536 : ℝ))) 3 (501323689601/1000000000000 : ℝ) (501323689609/1000000000000 : ℝ) (250655727969/500000000000 : ℝ) (250655727973/500000000000 : ℝ) (501317572769/1000000000000 : ℝ) (250658786389/500000000000 : ℝ) (125329393183/250000000000 : ℝ) (501317572741/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8369/65536 : ℝ))) 4 (501317572769/1000000000000 : ℝ) (250658786389/500000000000 : ℝ) (125329393183/250000000000 : ℝ) (501317572741/1000000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8369/65536 : ℝ))) 5 (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8369/65536 : ℝ))) 6 (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8369/65536 : ℝ))) 7 (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8369/65536 : ℝ)) hmem 8 (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8369/65536 : ℝ))) hcmem 8 (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8369/65536 : ℝ)) (198413252873/200000000000 : ℝ) (992066264369/1000000000000 : ℝ) (2005270291/4000000000 : ℝ) (12532939319/25000000000 : ℝ) (793765326083/1000000000000 : ℝ) (793765326103/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0879_exp_lower
  have heNumeric : (2054901537823/1000000000000 : ℝ)/4 ≤ Real.exp (-85256502756809/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901537823/1000000000000 : ℝ)/4 ≤ Real.exp ((66951/524288 : ℝ)-(793765326103/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66951/524288 : ℝ) (8369/65536 : ℝ) (793765326103/1000000000000 : ℝ) (2054901537823/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0880; no trusted numerical premise.
theorem cover8_leaf0880_exp_radius : (499003317253171179/500000000000000000 : ℝ) ≤ Real.exp ((-66953/4194304 : ℝ)/8) ∧ Real.exp ((-66953/4194304 : ℝ)/8) ≤ (998006634506342359/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66953/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0880_exp_lower : (184022689613182277/200000000000000000 : ℝ) ≤ Real.exp ((-426282513543/640000000000 : ℝ)/8) ∧ Real.exp ((-426282513543/640000000000 : ℝ)/8) ≤ (460056724032955693/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-426282513543/640000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0880_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901538597/1000000000000 : ℝ) ≤ 4*Real.exp (8369/65536 : ℝ)*Real.exp (-mu (radius 8 (66953/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901538597/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66953/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0880_exp_radius
  have hrNumeric : (196832778353/200000000000 : ℝ) ≤ Real.exp (-66953/4194304 : ℝ) ∧ Real.exp (-66953/4194304 : ℝ) ≤ (492081945883/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196832778353/200000000000 : ℝ) ≤ (radius 8 (66953/524288 : ℝ)) ∧ (radius 8 (66953/524288 : ℝ)) ≤ (492081945883/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66953/524288 : ℝ)) (196832778353/200000000000 : ℝ) (492081945883/500000000000 : ℝ) (35452184217/200000000000 : ℝ) (177260921091/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66953/524288 : ℝ)) (196832778353/200000000000 : ℝ) (492081945883/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66953/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196832778353/200000000000 : ℝ) (492081945883/500000000000 : ℝ) (496040972941/500000000000 : ℝ) (992081945883/1000000000000 : ℝ) (496025173697/500000000000 : ℝ) (198410069479/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66953/524288 : ℝ)) 1 (496040972941/500000000000 : ℝ) (992081945883/1000000000000 : ℝ) (496025173697/500000000000 : ℝ) (198410069479/200000000000 : ℝ) (496033073319/500000000000 : ℝ) (992066146639/1000000000000 : ℝ) (62004134157/62500000000 : ℝ) (496033073257/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66953/524288 : ℝ)) 2 (496033073319/500000000000 : ℝ) (992066146639/1000000000000 : ℝ) (62004134157/62500000000 : ℝ) (496033073257/500000000000 : ℝ) (39682645863/40000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66953/524288 : ℝ)) 3 (39682645863/40000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66953/524288 : ℝ)) 4 (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66953/524288 : ℝ)) 5 (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66953/524288 : ℝ)) 6 (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66953/524288 : ℝ)) 7 (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66953/524288 : ℝ))) (35452184217/200000000000 : ℝ) (177260921091/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66953/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35452184217/200000000000 : ℝ) (177260921091/1000000000000 : ℝ) (294315230271/500000000000 : ℝ) (294315230273/500000000000 : ℝ) (421023658581/1000000000000 : ℝ) (421023658589/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66953/524288 : ℝ))) 1 (294315230271/500000000000 : ℝ) (294315230273/500000000000 : ℝ) (421023658581/1000000000000 : ℝ) (421023658589/1000000000000 : ℝ) (504827059561/1000000000000 : ℝ) (31551691223/62500000000 : ℝ) (248911304509/500000000000 : ℝ) (19912904361/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66953/524288 : ℝ))) 2 (504827059561/1000000000000 : ℝ) (31551691223/62500000000 : ℝ) (248911304509/500000000000 : ℝ) (19912904361/40000000000 : ℝ) (501324834289/1000000000000 : ℝ) (501324834297/1000000000000 : ℝ) (125328150243/250000000000 : ℝ) (25065630049/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66953/524288 : ℝ))) 3 (501324834289/1000000000000 : ℝ) (501324834297/1000000000000 : ℝ) (125328150243/250000000000 : ℝ) (25065630049/50000000000 : ℝ) (50131871763/100000000000 : ℝ) (501318717639/1000000000000 : ℝ) (501318717593/1000000000000 : ℝ) (250659358801/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66953/524288 : ℝ))) 4 (50131871763/100000000000 : ℝ) (501318717639/1000000000000 : ℝ) (501318717593/1000000000000 : ℝ) (250659358801/500000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66953/524288 : ℝ))) 5 (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66953/524288 : ℝ))) 6 (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66953/524288 : ℝ))) 7 (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66953/524288 : ℝ)) hmem 8 (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66953/524288 : ℝ))) hcmem 8 (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66953/524288 : ℝ)) (496033073287/500000000000 : ℝ) (992066146577/1000000000000 : ℝ) (501318717611/1000000000000 : ℝ) (501318717621/1000000000000 : ℝ) (158753446611/200000000000 : ℝ) (31750689323/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0880_exp_lower
  have heNumeric : (2054901538597/1000000000000 : ℝ)/4 ≤ Real.exp (-426282513543/640000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901538597/1000000000000 : ℝ)/4 ≤ Real.exp ((8369/65536 : ℝ)-(31750689323/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8369/65536 : ℝ) (66953/524288 : ℝ) (31750689323/40000000000 : ℝ) (2054901538597/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0881; no trusted numerical premise.
theorem cover8_leaf0881_exp_radius : (499003302381713667/500000000000000000 : ℝ) ≤ Real.exp ((-33477/2097152 : ℝ)/8) ∧ Real.exp ((-33477/2097152 : ℝ)/8) ≤ (199601320952685467/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33477/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0881_exp_lower : (920113448111529783/1000000000000000000 : ℝ) ≤ Real.exp ((-85256502657831/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502657831/128000000000000 : ℝ)/8) ≤ (115014181013941223/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502657831/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0881_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725384853/250000000000 : ℝ) ≤ 4*Real.exp (66953/524288 : ℝ)*Real.exp (-mu (radius 8 (33477/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725384853/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33477/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0881_exp_radius
  have hrNumeric : (492081828561/500000000000 : ℝ) ≤ Real.exp (-33477/2097152 : ℝ) ∧ Real.exp (-33477/2097152 : ℝ) ≤ (984163657123/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492081828561/500000000000 : ℝ) ≤ (radius 8 (33477/262144 : ℝ)) ∧ (radius 8 (33477/262144 : ℝ)) ≤ (984163657123/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33477/262144 : ℝ)) (492081828561/500000000000 : ℝ) (984163657123/1000000000000 : ℝ) (177262223833/1000000000000 : ℝ) (177262223839/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33477/262144 : ℝ)) (492081828561/500000000000 : ℝ) (984163657123/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33477/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492081828561/500000000000 : ℝ) (984163657123/1000000000000 : ℝ) (992081828561/1000000000000 : ℝ) (496040914281/500000000000 : ℝ) (248012557283/250000000000 : ℝ) (496025114567/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33477/262144 : ℝ)) 1 (992081828561/1000000000000 : ℝ) (496040914281/500000000000 : ℝ) (248012557283/250000000000 : ℝ) (496025114567/500000000000 : ℝ) (496033014423/500000000000 : ℝ) (62004126803/62500000000 : ℝ) (12400825359/12500000000 : ℝ) (992066028723/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33477/262144 : ℝ)) 2 (496033014423/500000000000 : ℝ) (62004126803/62500000000 : ℝ) (12400825359/12500000000 : ℝ) (992066028723/1000000000000 : ℝ) (992066028783/1000000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33477/262144 : ℝ)) 3 (992066028783/1000000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33477/262144 : ℝ)) 4 (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33477/262144 : ℝ)) 5 (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33477/262144 : ℝ)) 6 (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33477/262144 : ℝ)) 7 (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33477/262144 : ℝ))) (177262223833/1000000000000 : ℝ) (177262223839/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33477/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177262223833/1000000000000 : ℝ) (177262223839/1000000000000 : ℝ) (147157777979/250000000000 : ℝ) (7357888899/12500000000 : ℝ) (421025205697/1000000000000 : ℝ) (210512602853/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33477/262144 : ℝ))) 1 (147157777979/250000000000 : ℝ) (7357888899/12500000000 : ℝ) (421025205697/1000000000000 : ℝ) (210512602853/500000000000 : ℝ) (252414079403/500000000000 : ℝ) (504828158813/1000000000000 : ℝ) (497823799123/1000000000000 : ℝ) (497823799131/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33477/262144 : ℝ))) 2 (252414079403/500000000000 : ℝ) (504828158813/1000000000000 : ℝ) (497823799123/1000000000000 : ℝ) (497823799131/1000000000000 : ℝ) (125331494741/250000000000 : ℝ) (125331494743/250000000000 : ℝ) (62664218249/125000000000 : ℝ) (501313746001/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33477/262144 : ℝ))) 3 (125331494741/250000000000 : ℝ) (125331494743/250000000000 : ℝ) (62664218249/125000000000 : ℝ) (501313746001/1000000000000 : ℝ) (250659931239/500000000000 : ℝ) (501319862487/1000000000000 : ℝ) (12532996561/25000000000 : ℝ) (10026397249/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33477/262144 : ℝ))) 4 (250659931239/500000000000 : ℝ) (501319862487/1000000000000 : ℝ) (12532996561/25000000000 : ℝ) (10026397249/20000000000 : ℝ) (501319862459/1000000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33477/262144 : ℝ))) 5 (501319862459/1000000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33477/262144 : ℝ))) 6 (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33477/262144 : ℝ))) 7 (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33477/262144 : ℝ)) hmem 8 (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33477/262144 : ℝ))) hcmem 8 (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33477/262144 : ℝ)) (496033014391/500000000000 : ℝ) (496033014393/500000000000 : ℝ) (250659931229/500000000000 : ℝ) (501319862469/1000000000000 : ℝ) (158753828001/200000000000 : ℝ) (793769140027/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0881_exp_lower
  have heNumeric : (513725384853/250000000000 : ℝ)/4 ≤ Real.exp (-85256502657831/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725384853/250000000000 : ℝ)/4 ≤ Real.exp ((66953/524288 : ℝ)-(793769140027/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66953/524288 : ℝ) (33477/262144 : ℝ) (793769140027/1000000000000 : ℝ) (513725384853/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0882; no trusted numerical premise.
theorem cover8_leaf0882_exp_radius : (998006575020513197/1000000000000000000 : ℝ) ≤ Real.exp ((-66955/4194304 : ℝ)/8) ∧ Real.exp ((-66955/4194304 : ℝ)/8) ≤ (499003287510256599/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66955/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0882_exp_lower : (18402268963186669/20000000000000000 : ℝ) ≤ Real.exp ((-8525650260463/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525650260463/12800000000000 : ℝ)/8) ≤ (920113448159333451/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525650260463/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0882_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450770133/500000000000 : ℝ) ≤ 4*Real.exp (33477/262144 : ℝ)*Real.exp (-mu (radius 8 (66955/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450770133/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66955/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0882_exp_radius
  have hrNumeric : (984163422479/1000000000000 : ℝ) ≤ Real.exp (-66955/4194304 : ℝ) ∧ Real.exp (-66955/4194304 : ℝ) ≤ (12302042781/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984163422479/1000000000000 : ℝ) ≤ (radius 8 (66955/524288 : ℝ)) ∧ (radius 8 (66955/524288 : ℝ)) ≤ (12302042781/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66955/524288 : ℝ)) (984163422479/1000000000000 : ℝ) (12302042781/12500000000 : ℝ) (177263526571/1000000000000 : ℝ) (177263526577/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66955/524288 : ℝ)) (984163422479/1000000000000 : ℝ) (12302042781/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66955/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984163422479/1000000000000 : ℝ) (12302042781/12500000000 : ℝ) (992081711239/1000000000000 : ℝ) (24802042781/25000000000 : ℝ) (99205011087/100000000000 : ℝ) (124006263859/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66955/524288 : ℝ)) 1 (992081711239/1000000000000 : ℝ) (24802042781/25000000000 : ℝ) (99205011087/100000000000 : ℝ) (124006263859/125000000000 : ℝ) (496032955527/500000000000 : ℝ) (62004119441/62500000000 : ℝ) (62004119433/62500000000 : ℝ) (992065910931/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66955/524288 : ℝ)) 2 (496032955527/500000000000 : ℝ) (62004119441/62500000000 : ℝ) (62004119433/62500000000 : ℝ) (992065910931/1000000000000 : ℝ) (992065910991/1000000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66955/524288 : ℝ)) 3 (992065910991/1000000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66955/524288 : ℝ)) 4 (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66955/524288 : ℝ)) 5 (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66955/524288 : ℝ)) 6 (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66955/524288 : ℝ)) 7 (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66955/524288 : ℝ))) (177263526571/1000000000000 : ℝ) (177263526577/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66955/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177263526571/1000000000000 : ℝ) (177263526577/1000000000000 : ℝ) (117726352657/200000000000 : ℝ) (588631763289/1000000000000 : ℝ) (421026752797/1000000000000 : ℝ) (84205350561/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66955/524288 : ℝ))) 1 (117726352657/200000000000 : ℝ) (588631763289/1000000000000 : ℝ) (421026752797/1000000000000 : ℝ) (84205350561/200000000000 : ℝ) (504829258041/1000000000000 : ℝ) (504829258047/1000000000000 : ℝ) (497824989217/1000000000000 : ℝ) (62228123653/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66955/524288 : ℝ))) 2 (504829258041/1000000000000 : ℝ) (504829258047/1000000000000 : ℝ) (497824989217/1000000000000 : ℝ) (62228123653/125000000000 : ℝ) (501327123629/1000000000000 : ℝ) (125331780909/250000000000 : ℝ) (250657445501/500000000000 : ℝ) (501314891009/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66955/524288 : ℝ))) 3 (501327123629/1000000000000 : ℝ) (125331780909/250000000000 : ℝ) (250657445501/500000000000 : ℝ) (501314891009/1000000000000 : ℝ) (100264201463/200000000000 : ℝ) (501321007323/1000000000000 : ℝ) (250660503639/500000000000 : ℝ) (250660503643/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66955/524288 : ℝ))) 4 (100264201463/200000000000 : ℝ) (501321007323/1000000000000 : ℝ) (250660503639/500000000000 : ℝ) (250660503643/500000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66955/524288 : ℝ))) 5 (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66955/524288 : ℝ))) 6 (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66955/524288 : ℝ))) 7 (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66955/524288 : ℝ)) hmem 8 (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66955/524288 : ℝ))) hcmem 8 (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66955/524288 : ℝ)) (99206591099/100000000000 : ℝ) (496032955497/500000000000 : ℝ) (7833140739/15625000000 : ℝ) (100264201461/200000000000 : ℝ) (396885523471/500000000000 : ℝ) (9922138087/12500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0882_exp_lower
  have heNumeric : (1027450770133/500000000000 : ℝ)/4 ≤ Real.exp (-8525650260463/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450770133/500000000000 : ℝ)/4 ≤ Real.exp ((33477/262144 : ℝ)-(9922138087/12500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33477/262144 : ℝ) (66955/524288 : ℝ) (9922138087/12500000000 : ℝ) (1027450770133/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0883; no trusted numerical premise.
theorem cover8_leaf0883_exp_radius : (998006545277599947/1000000000000000000 : ℝ) ≤ Real.exp ((-16739/1048576 : ℝ)/8) ∧ Real.exp ((-16739/1048576 : ℝ)/8) ≤ (249501636319399987/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16739/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0883_exp_lower : (920113448209207373/1000000000000000000 : ℝ) ≤ Real.exp ((-682052020393/1024000000000 : ℝ)/8) ∧ Real.exp ((-682052020393/1024000000000 : ℝ)/8) ≤ (460056724104603687/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-682052020393/1024000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0883_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901541157/1000000000000 : ℝ) ≤ 4*Real.exp (66955/524288 : ℝ)*Real.exp (-mu (radius 8 (16739/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901541157/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16739/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0883_exp_radius
  have hrNumeric : (246040796959/250000000000 : ℝ) ≤ Real.exp (-16739/1048576 : ℝ) ∧ Real.exp (-16739/1048576 : ℝ) ≤ (984163187837/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246040796959/250000000000 : ℝ) ≤ (radius 8 (16739/131072 : ℝ)) ∧ (radius 8 (16739/131072 : ℝ)) ≤ (984163187837/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16739/131072 : ℝ)) (246040796959/250000000000 : ℝ) (984163187837/1000000000000 : ℝ) (177264829299/1000000000000 : ℝ) (35452965861/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16739/131072 : ℝ)) (246040796959/250000000000 : ℝ) (984163187837/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16739/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246040796959/250000000000 : ℝ) (984163187837/1000000000000 : ℝ) (496040796959/500000000000 : ℝ) (992081593919/1000000000000 : ℝ) (992049992609/1000000000000 : ℝ) (99204999261/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16739/131072 : ℝ)) 1 (496040796959/500000000000 : ℝ) (992081593919/1000000000000 : ℝ) (992049992609/1000000000000 : ℝ) (99204999261/100000000000 : ℝ) (992065793263/1000000000000 : ℝ) (198413158653/200000000000 : ℝ) (992065793137/1000000000000 : ℝ) (992065793139/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16739/131072 : ℝ)) 2 (992065793263/1000000000000 : ℝ) (198413158653/200000000000 : ℝ) (992065793137/1000000000000 : ℝ) (992065793139/1000000000000 : ℝ) (2480164483/2500000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16739/131072 : ℝ)) 3 (2480164483/2500000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16739/131072 : ℝ)) 4 (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16739/131072 : ℝ)) 5 (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16739/131072 : ℝ)) 6 (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16739/131072 : ℝ)) 7 (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16739/131072 : ℝ))) (177264829299/1000000000000 : ℝ) (35452965861/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16739/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177264829299/1000000000000 : ℝ) (35452965861/200000000000 : ℝ) (588632414649/1000000000000 : ℝ) (588632414653/1000000000000 : ℝ) (210514149939/500000000000 : ℝ) (421028299887/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16739/131072 : ℝ))) 1 (588632414649/1000000000000 : ℝ) (588632414653/1000000000000 : ℝ) (210514149939/500000000000 : ℝ) (421028299887/1000000000000 : ℝ) (504830357263/1000000000000 : ℝ) (50483035727/100000000000 : ℝ) (15557068103/31250000000 : ℝ) (62228272413/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16739/131072 : ℝ))) 2 (504830357263/1000000000000 : ℝ) (50483035727/100000000000 : ℝ) (15557068103/31250000000 : ℝ) (62228272413/125000000000 : ℝ) (501328268279/1000000000000 : ℝ) (501328268287/1000000000000 : ℝ) (250658017999/500000000000 : ℝ) (250658018003/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16739/131072 : ℝ))) 3 (501328268279/1000000000000 : ℝ) (501328268287/1000000000000 : ℝ) (250658017999/500000000000 : ℝ) (250658018003/500000000000 : ℝ) (250661076069/500000000000 : ℝ) (501322152147/1000000000000 : ℝ) (501322152101/1000000000000 : ℝ) (50132215211/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16739/131072 : ℝ))) 4 (250661076069/500000000000 : ℝ) (501322152147/1000000000000 : ℝ) (501322152101/1000000000000 : ℝ) (50132215211/100000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16739/131072 : ℝ))) 5 (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16739/131072 : ℝ))) 6 (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16739/131072 : ℝ))) 7 (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16739/131072 : ℝ)) hmem 8 (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16739/131072 : ℝ))) hcmem 8 (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16739/131072 : ℝ)) (992065793199/1000000000000 : ℝ) (496032896601/500000000000 : ℝ) (501322152119/1000000000000 : ℝ) (501322152129/1000000000000 : ℝ) (158754590771/200000000000 : ℝ) (6350183631/8000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0883_exp_lower
  have heNumeric : (2054901541157/1000000000000 : ℝ)/4 ≤ Real.exp (-682052020393/1024000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901541157/1000000000000 : ℝ)/4 ≤ Real.exp ((66955/524288 : ℝ)-(6350183631/8000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66955/524288 : ℝ) (16739/131072 : ℝ) (6350183631/8000000000 : ℝ) (2054901541157/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0884; no trusted numerical premise.
theorem cover8_leaf0884_exp_radius : (499003257767343791/500000000000000000 : ℝ) ≤ Real.exp ((-66957/4194304 : ℝ)/8) ∧ Real.exp ((-66957/4194304 : ℝ)/8) ≤ (998006515534687583/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66957/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0884_exp_lower : (920113448262416707/1000000000000000000 : ℝ) ≤ Real.exp ((-21314125622477/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125622477/32000000000000 : ℝ)/8) ≤ (230028362065604177/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125622477/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0884_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725385527/250000000000 : ℝ) ≤ 4*Real.exp (16739/131072 : ℝ)*Real.exp (-mu (radius 8 (66957/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725385527/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66957/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0884_exp_radius
  have hrNumeric : (492081476597/500000000000 : ℝ) ≤ Real.exp (-66957/4194304 : ℝ) ∧ Real.exp (-66957/4194304 : ℝ) ≤ (196832590639/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492081476597/500000000000 : ℝ) ≤ (radius 8 (66957/524288 : ℝ)) ∧ (radius 8 (66957/524288 : ℝ)) ≤ (196832590639/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66957/524288 : ℝ)) (492081476597/500000000000 : ℝ) (196832590639/200000000000 : ℝ) (44316533003/250000000000 : ℝ) (88633066009/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66957/524288 : ℝ)) (492081476597/500000000000 : ℝ) (196832590639/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66957/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492081476597/500000000000 : ℝ) (196832590639/200000000000 : ℝ) (992081476597/1000000000000 : ℝ) (496040738299/500000000000 : ℝ) (248012468587/250000000000 : ℝ) (992049874349/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66957/524288 : ℝ)) 1 (992081476597/1000000000000 : ℝ) (496040738299/500000000000 : ℝ) (248012468587/250000000000 : ℝ) (992049874349/1000000000000 : ℝ) (62004104717/62500000000 : ℝ) (496032837737/500000000000 : ℝ) (496032837673/500000000000 : ℝ) (248016418837/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66957/524288 : ℝ)) 2 (62004104717/62500000000 : ℝ) (496032837737/500000000000 : ℝ) (496032837673/500000000000 : ℝ) (248016418837/250000000000 : ℝ) (992065675409/1000000000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66957/524288 : ℝ)) 3 (992065675409/1000000000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66957/524288 : ℝ)) 4 (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66957/524288 : ℝ)) 5 (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66957/524288 : ℝ)) 6 (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66957/524288 : ℝ)) 7 (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66957/524288 : ℝ))) (44316533003/250000000000 : ℝ) (88633066009/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66957/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44316533003/250000000000 : ℝ) (88633066009/500000000000 : ℝ) (294316533003/500000000000 : ℝ) (588633066009/1000000000000 : ℝ) (421029846937/1000000000000 : ℝ) (84205969389/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66957/524288 : ℝ))) 1 (294316533003/500000000000 : ℝ) (588633066009/1000000000000 : ℝ) (421029846937/1000000000000 : ℝ) (84205969389/200000000000 : ℝ) (504831456471/1000000000000 : ℝ) (504831456477/1000000000000 : ℝ) (248913684679/500000000000 : ℝ) (99565473873/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66957/524288 : ℝ))) 2 (504831456471/1000000000000 : ℝ) (504831456477/1000000000000 : ℝ) (248913684679/500000000000 : ℝ) (99565473873/200000000000 : ℝ) (250664706457/500000000000 : ℝ) (501329412921/1000000000000 : ℝ) (250658590489/500000000000 : ℝ) (100263436197/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66957/524288 : ℝ))) 3 (250664706457/500000000000 : ℝ) (501329412921/1000000000000 : ℝ) (250658590489/500000000000 : ℝ) (100263436197/200000000000 : ℝ) (250661648473/500000000000 : ℝ) (501323296953/1000000000000 : ℝ) (125330824227/250000000000 : ℝ) (125330824229/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66957/524288 : ℝ))) 4 (250661648473/500000000000 : ℝ) (501323296953/1000000000000 : ℝ) (125330824227/250000000000 : ℝ) (125330824229/250000000000 : ℝ) (501323296927/1000000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66957/524288 : ℝ))) 5 (501323296927/1000000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66957/524288 : ℝ))) 6 (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66957/524288 : ℝ))) 7 (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66957/524288 : ℝ)) hmem 8 (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66957/524288 : ℝ))) hcmem 8 (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66957/524288 : ℝ)) (62004104713/62500000000 : ℝ) (992065675411/1000000000000 : ℝ) (250661648463/500000000000 : ℝ) (100264659387/200000000000 : ℝ) (793774860743/1000000000000 : ℝ) (793774860761/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0884_exp_lower
  have heNumeric : (513725385527/250000000000 : ℝ)/4 ≤ Real.exp (-21314125622477/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725385527/250000000000 : ℝ)/4 ≤ Real.exp ((16739/131072 : ℝ)-(793774860761/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16739/131072 : ℝ) (66957/524288 : ℝ) (793774860761/1000000000000 : ℝ) (513725385527/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0885; no trusted numerical premise.
theorem cover8_leaf0885_exp_radius : (199601297158355221/200000000000000000 : ℝ) ≤ Real.exp ((-33479/2097152 : ℝ)/8) ∧ Real.exp ((-33479/2097152 : ℝ)/8) ≤ (499003242895888053/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33479/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0885_exp_lower : (184022689663309231/200000000000000000 : ℝ) ≤ Real.exp ((-85256502429667/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502429667/128000000000000 : ℝ)/8) ≤ (230028362079136539/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502429667/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0885_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (82196061723/40000000000 : ℝ) ≤ 4*Real.exp (66957/524288 : ℝ)*Real.exp (-mu (radius 8 (33479/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (82196061723/40000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33479/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0885_exp_radius
  have hrNumeric : (984162718551/1000000000000 : ℝ) ≤ Real.exp (-33479/2097152 : ℝ) ∧ Real.exp (-33479/2097152 : ℝ) ≤ (123020339819/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984162718551/1000000000000 : ℝ) ≤ (radius 8 (33479/262144 : ℝ)) ∧ (radius 8 (33479/262144 : ℝ)) ≤ (123020339819/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33479/262144 : ℝ)) (984162718551/1000000000000 : ℝ) (123020339819/125000000000 : ℝ) (1107921467/6250000000 : ℝ) (88633717363/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33479/262144 : ℝ)) (984162718551/1000000000000 : ℝ) (123020339819/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33479/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984162718551/1000000000000 : ℝ) (123020339819/125000000000 : ℝ) (39683254371/40000000000 : ℝ) (248020339819/250000000000 : ℝ) (496024878043/500000000000 : ℝ) (992049756087/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33479/262144 : ℝ)) 1 (39683254371/40000000000 : ℝ) (248020339819/250000000000 : ℝ) (496024878043/500000000000 : ℝ) (992049756087/1000000000000 : ℝ) (12400819471/12500000000 : ℝ) (496032778841/500000000000 : ℝ) (496032778777/500000000000 : ℝ) (248016389389/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33479/262144 : ℝ)) 2 (12400819471/12500000000 : ℝ) (496032778841/500000000000 : ℝ) (496032778777/500000000000 : ℝ) (248016389389/250000000000 : ℝ) (992065557617/1000000000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33479/262144 : ℝ)) 3 (992065557617/1000000000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33479/262144 : ℝ)) 4 (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33479/262144 : ℝ)) 5 (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33479/262144 : ℝ)) 6 (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33479/262144 : ℝ)) 7 (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33479/262144 : ℝ))) (1107921467/6250000000 : ℝ) (88633717363/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33479/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1107921467/6250000000 : ℝ) (88633717363/500000000000 : ℝ) (7357921467/12500000000 : ℝ) (588633717363/1000000000000 : ℝ) (421031393983/1000000000000 : ℝ) (421031393991/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33479/262144 : ℝ))) 1 (7357921467/12500000000 : ℝ) (588633717363/1000000000000 : ℝ) (421031393983/1000000000000 : ℝ) (421031393991/1000000000000 : ℝ) (504832555671/1000000000000 : ℝ) (504832555677/1000000000000 : ℝ) (497828559411/1000000000000 : ℝ) (248914279709/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33479/262144 : ℝ))) 2 (504832555671/1000000000000 : ℝ) (504832555677/1000000000000 : ℝ) (497828559411/1000000000000 : ℝ) (248914279709/500000000000 : ℝ) (501330557541/1000000000000 : ℝ) (125332639387/250000000000 : ℝ) (10026366519/20000000000 : ℝ) (501318325957/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33479/262144 : ℝ))) 3 (501330557541/1000000000000 : ℝ) (125332639387/250000000000 : ℝ) (10026366519/20000000000 : ℝ) (501318325957/1000000000000 : ℝ) (100264888349/200000000000 : ℝ) (501324441753/1000000000000 : ℝ) (125331110427/250000000000 : ℝ) (125331110429/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33479/262144 : ℝ))) 4 (100264888349/200000000000 : ℝ) (501324441753/1000000000000 : ℝ) (125331110427/250000000000 : ℝ) (125331110429/250000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33479/262144 : ℝ))) 5 (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33479/262144 : ℝ))) 6 (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33479/262144 : ℝ))) 7 (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33479/262144 : ℝ)) hmem 8 (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33479/262144 : ℝ))) hcmem 8 (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33479/262144 : ℝ)) (62004097351/62500000000 : ℝ) (992065557619/1000000000000 : ℝ) (250662220863/500000000000 : ℝ) (100264888347/200000000000 : ℝ) (793776767621/1000000000000 : ℝ) (793776767639/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0885_exp_lower
  have heNumeric : (82196061723/40000000000 : ℝ)/4 ≤ Real.exp (-85256502429667/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (82196061723/40000000000 : ℝ)/4 ≤ Real.exp ((66957/524288 : ℝ)-(793776767639/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66957/524288 : ℝ) (33479/262144 : ℝ) (793776767639/1000000000000 : ℝ) (82196061723/40000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0886; no trusted numerical premise.
theorem cover8_leaf0886_exp_radius : (998006456048865513/1000000000000000000 : ℝ) ≤ Real.exp ((-66959/4194304 : ℝ)/8) ∧ Real.exp ((-66959/4194304 : ℝ)/8) ≤ (499003228024432757/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66959/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0886_exp_lower : (115014181046607609/125000000000000000 : ℝ) ≤ Real.exp ((-42628251183497/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251183497/64000000000000 : ℝ)/8) ≤ (920113448372860873/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251183497/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0886_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901544081/1000000000000 : ℝ) ≤ 4*Real.exp (33479/262144 : ℝ)*Real.exp (-mu (radius 8 (66959/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901544081/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66959/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0886_exp_radius
  have hrNumeric : (246040620977/250000000000 : ℝ) ≤ Real.exp (-66959/4194304 : ℝ) ∧ Real.exp (-66959/4194304 : ℝ) ≤ (984162483909/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246040620977/250000000000 : ℝ) ≤ (radius 8 (66959/524288 : ℝ)) ∧ (radius 8 (66959/524288 : ℝ)) ≤ (984162483909/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66959/524288 : ℝ)) (246040620977/250000000000 : ℝ) (984162483909/1000000000000 : ℝ) (88634368709/500000000000 : ℝ) (7090749497/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66959/524288 : ℝ)) (246040620977/250000000000 : ℝ) (984162483909/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66959/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246040620977/250000000000 : ℝ) (984162483909/1000000000000 : ℝ) (496040620977/500000000000 : ℝ) (198416248391/200000000000 : ℝ) (15500775591/15625000000 : ℝ) (496024818913/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66959/524288 : ℝ)) 1 (496040620977/500000000000 : ℝ) (198416248391/200000000000 : ℝ) (15500775591/15625000000 : ℝ) (496024818913/500000000000 : ℝ) (992065439889/1000000000000 : ℝ) (992065439891/1000000000000 : ℝ) (992065439763/1000000000000 : ℝ) (198413087953/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66959/524288 : ℝ)) 2 (992065439889/1000000000000 : ℝ) (992065439891/1000000000000 : ℝ) (992065439763/1000000000000 : ℝ) (198413087953/200000000000 : ℝ) (496032719913/500000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66959/524288 : ℝ)) 3 (496032719913/500000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66959/524288 : ℝ)) 4 (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66959/524288 : ℝ)) 5 (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66959/524288 : ℝ)) 6 (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66959/524288 : ℝ)) 7 (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66959/524288 : ℝ))) (88634368709/500000000000 : ℝ) (7090749497/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66959/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88634368709/500000000000 : ℝ) (7090749497/40000000000 : ℝ) (588634368709/1000000000000 : ℝ) (588634368713/1000000000000 : ℝ) (105258235253/250000000000 : ℝ) (210516470511/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66959/524288 : ℝ))) 1 (588634368709/1000000000000 : ℝ) (588634368713/1000000000000 : ℝ) (105258235253/250000000000 : ℝ) (210516470511/500000000000 : ℝ) (25241682743/50000000000 : ℝ) (126208413717/250000000000 : ℝ) (9956594989/20000000000 : ℝ) (497829749459/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66959/524288 : ℝ))) 2 (25241682743/50000000000 : ℝ) (126208413717/250000000000 : ℝ) (9956594989/20000000000 : ℝ) (497829749459/1000000000000 : ℝ) (100266340431/200000000000 : ℝ) (125332925541/250000000000 : ℝ) (501319470909/1000000000000 : ℝ) (250659735459/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66959/524288 : ℝ))) 3 (100266340431/200000000000 : ℝ) (125332925541/250000000000 : ℝ) (501319470909/1000000000000 : ℝ) (250659735459/500000000000 : ℝ) (125331396633/250000000000 : ℝ) (501325586541/1000000000000 : ℝ) (250662793247/500000000000 : ℝ) (62665698313/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66959/524288 : ℝ))) 4 (125331396633/250000000000 : ℝ) (501325586541/1000000000000 : ℝ) (250662793247/500000000000 : ℝ) (62665698313/125000000000 : ℝ) (501325586513/1000000000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66959/524288 : ℝ))) 5 (501325586513/1000000000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66959/524288 : ℝ))) 6 (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66959/524288 : ℝ))) 7 (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66959/524288 : ℝ)) hmem 8 (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66959/524288 : ℝ))) hcmem 8 (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66959/524288 : ℝ)) (39682617593/40000000000 : ℝ) (248016359957/250000000000 : ℝ) (31332849157/62500000000 : ℝ) (501325586523/1000000000000 : ℝ) (793778674477/1000000000000 : ℝ) (396889337249/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0886_exp_lower
  have heNumeric : (2054901544081/1000000000000 : ℝ)/4 ≤ Real.exp (-42628251183497/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901544081/1000000000000 : ℝ)/4 ≤ Real.exp ((33479/262144 : ℝ)-(396889337249/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33479/262144 : ℝ) (66959/524288 : ℝ) (396889337249/500000000000 : ℝ) (2054901544081/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0887; no trusted numerical premise.
theorem cover8_leaf0887_exp_radius : (31187700822061119/31250000000000000 : ℝ) ≤ Real.exp ((-4185/262144 : ℝ)/8) ∧ Real.exp ((-4185/262144 : ℝ)/8) ≤ (998006426305955809/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4185/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0887_exp_lower : (920113448432511/1000000000000000 : ℝ) ≤ Real.exp ((-85256502300609/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502300609/128000000000000 : ℝ)/8) ≤ (920113448432511001/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502300609/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0887_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901545147/1000000000000 : ℝ) ≤ 4*Real.exp (66959/524288 : ℝ)*Real.exp (-mu (radius 8 (4185/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901545147/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4185/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0887_exp_radius
  have hrNumeric : (492081124633/500000000000 : ℝ) ≤ Real.exp (-4185/262144 : ℝ) ∧ Real.exp (-4185/262144 : ℝ) ≤ (984162249267/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492081124633/500000000000 : ℝ) ≤ (radius 8 (4185/32768 : ℝ)) ∧ (radius 8 (4185/32768 : ℝ)) ≤ (984162249267/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4185/32768 : ℝ)) (492081124633/500000000000 : ℝ) (984162249267/1000000000000 : ℝ) (177270040101/1000000000000 : ℝ) (44317510027/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4185/32768 : ℝ)) (492081124633/500000000000 : ℝ) (984162249267/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4185/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492081124633/500000000000 : ℝ) (984162249267/1000000000000 : ℝ) (992081124633/1000000000000 : ℝ) (496040562317/500000000000 : ℝ) (992049519563/1000000000000 : ℝ) (248012379891/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4185/32768 : ℝ)) 1 (992081124633/1000000000000 : ℝ) (496040562317/500000000000 : ℝ) (992049519563/1000000000000 : ℝ) (248012379891/250000000000 : ℝ) (496032661049/500000000000 : ℝ) (992065322099/1000000000000 : ℝ) (248016330493/250000000000 : ℝ) (496032660987/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4185/32768 : ℝ)) 2 (496032661049/500000000000 : ℝ) (992065322099/1000000000000 : ℝ) (248016330493/250000000000 : ℝ) (496032660987/500000000000 : ℝ) (198413064407/200000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4185/32768 : ℝ)) 3 (198413064407/200000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4185/32768 : ℝ)) 4 (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4185/32768 : ℝ)) 5 (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4185/32768 : ℝ)) 6 (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4185/32768 : ℝ)) 7 (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4185/32768 : ℝ))) (177270040101/1000000000000 : ℝ) (44317510027/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4185/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177270040101/1000000000000 : ℝ) (44317510027/250000000000 : ℝ) (11772700401/20000000000 : ℝ) (294317510027/500000000000 : ℝ) (210517244009/500000000000 : ℝ) (421034488027/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4185/32768 : ℝ))) 1 (11772700401/20000000000 : ℝ) (294317510027/500000000000 : ℝ) (210517244009/500000000000 : ℝ) (421034488027/1000000000000 : ℝ) (252417377017/500000000000 : ℝ) (504834754041/1000000000000 : ℝ) (31114433717/62500000000 : ℝ) (12445773487/25000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4185/32768 : ℝ))) 2 (252417377017/500000000000 : ℝ) (504834754041/1000000000000 : ℝ) (31114433717/62500000000 : ℝ) (12445773487/25000000000 : ℝ) (501332846753/1000000000000 : ℝ) (501332846761/1000000000000 : ℝ) (125330153963/250000000000 : ℝ) (501320615861/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4185/32768 : ℝ))) 3 (501332846753/1000000000000 : ℝ) (501332846761/1000000000000 : ℝ) (125330153963/250000000000 : ℝ) (501320615861/1000000000000 : ℝ) (250663365651/500000000000 : ℝ) (501326731311/1000000000000 : ℝ) (100265346253/200000000000 : ℝ) (250663365637/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4185/32768 : ℝ))) 4 (250663365651/500000000000 : ℝ) (501326731311/1000000000000 : ℝ) (100265346253/200000000000 : ℝ) (250663365637/500000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4185/32768 : ℝ))) 5 (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4185/32768 : ℝ))) 6 (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4185/32768 : ℝ))) 7 (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4185/32768 : ℝ)) hmem 8 (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4185/32768 : ℝ))) hcmem 8 (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4185/32768 : ℝ)) (496032661017/500000000000 : ℝ) (992065322037/1000000000000 : ℝ) (501326731283/1000000000000 : ℝ) (501326731293/1000000000000 : ℝ) (793780581309/1000000000000 : ℝ) (49611286333/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0887_exp_lower
  have heNumeric : (2054901545147/1000000000000 : ℝ)/4 ≤ Real.exp (-85256502300609/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901545147/1000000000000 : ℝ)/4 ≤ Real.exp ((66959/524288 : ℝ)-(49611286333/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66959/524288 : ℝ) (4185/32768 : ℝ) (49611286333/62500000000 : ℝ) (2054901545147/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0888; no trusted numerical premise.
theorem cover8_leaf0888_exp_radius : (99800639656304699/100000000000000000 : ℝ) ≤ Real.exp ((-66961/4194304 : ℝ)/8) ∧ Real.exp ((-66961/4194304 : ℝ)/8) ≤ (998006396563046991/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66961/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0888_exp_lower : (28753545265412383/31250000000000000 : ℝ) ≤ Real.exp ((-5328531389567/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328531389567/8000000000000 : ℝ)/8) ≤ (920113448493196257/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328531389567/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0888_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901546231/1000000000000 : ℝ) ≤ 4*Real.exp (4185/32768 : ℝ)*Real.exp (-mu (radius 8 (66961/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901546231/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66961/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0888_exp_radius
  have hrNumeric : (984162014623/1000000000000 : ℝ) ≤ Real.exp (-66961/4194304 : ℝ) ∧ Real.exp (-66961/4194304 : ℝ) ≤ (30755062957/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984162014623/1000000000000 : ℝ) ≤ (radius 8 (66961/524288 : ℝ)) ∧ (radius 8 (66961/524288 : ℝ)) ≤ (30755062957/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66961/524288 : ℝ)) (984162014623/1000000000000 : ℝ) (30755062957/31250000000 : ℝ) (8863567139/50000000000 : ℝ) (177271342787/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66961/524288 : ℝ)) (984162014623/1000000000000 : ℝ) (30755062957/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66961/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984162014623/1000000000000 : ℝ) (30755062957/31250000000 : ℝ) (992081007311/1000000000000 : ℝ) (62005062957/62500000000 : ℝ) (992049401301/1000000000000 : ℝ) (992049401303/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66961/524288 : ℝ)) 1 (992081007311/1000000000000 : ℝ) (62005062957/62500000000 : ℝ) (992049401301/1000000000000 : ℝ) (992049401303/1000000000000 : ℝ) (496032602153/500000000000 : ℝ) (248016301077/250000000000 : ℝ) (49603260209/50000000000 : ℝ) (496032602091/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66961/524288 : ℝ)) 2 (496032602153/500000000000 : ℝ) (248016301077/250000000000 : ℝ) (49603260209/50000000000 : ℝ) (496032602091/500000000000 : ℝ) (992065204243/1000000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66961/524288 : ℝ)) 3 (992065204243/1000000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66961/524288 : ℝ)) 4 (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66961/524288 : ℝ)) 5 (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66961/524288 : ℝ)) 6 (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66961/524288 : ℝ)) 7 (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66961/524288 : ℝ))) (8863567139/50000000000 : ℝ) (177271342787/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66961/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8863567139/50000000000 : ℝ) (177271342787/1000000000000 : ℝ) (58863567139/100000000000 : ℝ) (294317835697/500000000000 : ℝ) (421036035013/1000000000000 : ℝ) (210518017511/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66961/524288 : ℝ))) 1 (58863567139/100000000000 : ℝ) (294317835697/500000000000 : ℝ) (421036035013/1000000000000 : ℝ) (210518017511/500000000000 : ℝ) (504835853201/1000000000000 : ℝ) (63104481651/125000000000 : ℝ) (248916064743/500000000000 : ℝ) (248916064747/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66961/524288 : ℝ))) 2 (504835853201/1000000000000 : ℝ) (63104481651/125000000000 : ℝ) (248916064743/500000000000 : ℝ) (248916064747/500000000000 : ℝ) (501333991343/1000000000000 : ℝ) (501333991351/1000000000000 : ℝ) (125330440197/250000000000 : ℝ) (125330440199/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66961/524288 : ℝ))) 3 (501333991343/1000000000000 : ℝ) (501333991351/1000000000000 : ℝ) (125330440197/250000000000 : ℝ) (125330440199/250000000000 : ℝ) (100265575213/200000000000 : ℝ) (250663938037/500000000000 : ℝ) (125331969007/250000000000 : ℝ) (501327876037/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66961/524288 : ℝ))) 4 (100265575213/200000000000 : ℝ) (250663938037/500000000000 : ℝ) (125331969007/250000000000 : ℝ) (501327876037/1000000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66961/524288 : ℝ))) 5 (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66961/524288 : ℝ))) 6 (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66961/524288 : ℝ))) 7 (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66961/524288 : ℝ)) hmem 8 (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66961/524288 : ℝ))) hcmem 8 (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66961/524288 : ℝ)) (496032602121/500000000000 : ℝ) (198413040849/200000000000 : ℝ) (250663938023/500000000000 : ℝ) (62665984507/125000000000 : ℝ) (79378248813/100000000000 : ℝ) (793782488149/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0888_exp_lower
  have heNumeric : (2054901546231/1000000000000 : ℝ)/4 ≤ Real.exp (-5328531389567/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901546231/1000000000000 : ℝ)/4 ≤ Real.exp ((4185/32768 : ℝ)-(793782488149/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4185/32768 : ℝ) (66961/524288 : ℝ) (793782488149/1000000000000 : ℝ) (2054901546231/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0889; no trusted numerical premise.
theorem cover8_leaf0889_exp_radius : (998006366820139057/1000000000000000000 : ℝ) ≤ Real.exp ((-33481/2097152 : ℝ)/8) ∧ Real.exp ((-33481/2097152 : ℝ)/8) ≤ (499003183410069529/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33481/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0889_exp_lower : (920113448557101909/1000000000000000000 : ℝ) ≤ Real.exp ((-85256502161951/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502161951/128000000000000 : ℝ)/8) ≤ (92011344855710191/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502161951/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0889_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901547373/1000000000000 : ℝ) ≤ 4*Real.exp (66961/524288 : ℝ)*Real.exp (-mu (radius 8 (33481/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901547373/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33481/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0889_exp_radius
  have hrNumeric : (984161779981/1000000000000 : ℝ) ≤ Real.exp (-33481/2097152 : ℝ) ∧ Real.exp (-33481/2097152 : ℝ) ≤ (492080889991/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984161779981/1000000000000 : ℝ) ≤ (radius 8 (33481/262144 : ℝ)) ∧ (radius 8 (33481/262144 : ℝ)) ≤ (492080889991/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33481/262144 : ℝ)) (984161779981/1000000000000 : ℝ) (492080889991/500000000000 : ℝ) (177272645443/1000000000000 : ℝ) (3545452909/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33481/262144 : ℝ)) (984161779981/1000000000000 : ℝ) (492080889991/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33481/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984161779981/1000000000000 : ℝ) (492080889991/500000000000 : ℝ) (99208088999/100000000000 : ℝ) (992080889991/1000000000000 : ℝ) (6200308019/6250000000 : ℝ) (992049283041/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33481/262144 : ℝ)) 1 (99208088999/100000000000 : ℝ) (992080889991/1000000000000 : ℝ) (6200308019/6250000000 : ℝ) (992049283041/1000000000000 : ℝ) (198413017303/200000000000 : ℝ) (248016271629/250000000000 : ℝ) (992065086389/1000000000000 : ℝ) (992065086391/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33481/262144 : ℝ)) 2 (198413017303/200000000000 : ℝ) (248016271629/250000000000 : ℝ) (992065086389/1000000000000 : ℝ) (992065086391/1000000000000 : ℝ) (248016271613/250000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33481/262144 : ℝ)) 3 (248016271613/250000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33481/262144 : ℝ)) 4 (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33481/262144 : ℝ)) 5 (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33481/262144 : ℝ)) 6 (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33481/262144 : ℝ)) 7 (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33481/262144 : ℝ))) (177272645443/1000000000000 : ℝ) (3545452909/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33481/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177272645443/1000000000000 : ℝ) (3545452909/20000000000 : ℝ) (588636322721/1000000000000 : ℝ) (23545452909/40000000000 : ℝ) (13157424437/31250000000 : ℝ) (421037581993/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33481/262144 : ℝ))) 1 (588636322721/1000000000000 : ℝ) (23545452909/40000000000 : ℝ) (13157424437/31250000000 : ℝ) (421037581993/1000000000000 : ℝ) (15776154761/31250000000 : ℝ) (504836952359/1000000000000 : ℝ) (497833319481/1000000000000 : ℝ) (497833319489/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33481/262144 : ℝ))) 2 (15776154761/31250000000 : ℝ) (504836952359/1000000000000 : ℝ) (497833319481/1000000000000 : ℝ) (497833319489/1000000000000 : ℝ) (125333783979/250000000000 : ℝ) (125333783981/250000000000 : ℝ) (250661452853/500000000000 : ℝ) (100264581143/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33481/262144 : ℝ))) 3 (125333783979/250000000000 : ℝ) (125333783981/250000000000 : ℝ) (250661452853/500000000000 : ℝ) (100264581143/200000000000 : ℝ) (501329020811/1000000000000 : ℝ) (25066451041/50000000000 : ℝ) (501329020773/1000000000000 : ℝ) (501329020783/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33481/262144 : ℝ))) 4 (501329020811/1000000000000 : ℝ) (25066451041/50000000000 : ℝ) (501329020773/1000000000000 : ℝ) (501329020783/1000000000000 : ℝ) (62666127599/125000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33481/262144 : ℝ))) 5 (62666127599/125000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33481/262144 : ℝ))) 6 (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33481/262144 : ℝ))) 7 (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33481/262144 : ℝ)) hmem 8 (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33481/262144 : ℝ))) hcmem 8 (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33481/262144 : ℝ)) (992065086451/1000000000000 : ℝ) (496032543227/500000000000 : ℝ) (501329020791/1000000000000 : ℝ) (250664510401/500000000000 : ℝ) (396892197461/500000000000 : ℝ) (396892197471/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0889_exp_lower
  have heNumeric : (2054901547373/1000000000000 : ℝ)/4 ≤ Real.exp (-85256502161951/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901547373/1000000000000 : ℝ)/4 ≤ Real.exp ((66961/524288 : ℝ)-(396892197471/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66961/524288 : ℝ) (33481/262144 : ℝ) (396892197471/500000000000 : ℝ) (2054901547373/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0890; no trusted numerical premise.
theorem cover8_leaf0890_exp_radius : (249501584269308003/250000000000000000 : ℝ) ≤ Real.exp ((-66963/4194304 : ℝ)/8) ∧ Real.exp ((-66963/4194304 : ℝ)/8) ≤ (998006337077232013/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66963/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0890_exp_lower : (920113448622042689/1000000000000000000 : ℝ) ≤ Real.exp ((-42628251044839/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628251044839/64000000000000 : ℝ)/8) ≤ (92011344862204269/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628251044839/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0890_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901548533/1000000000000 : ℝ) ≤ 4*Real.exp (33481/262144 : ℝ)*Real.exp (-mu (radius 8 (66963/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901548533/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66963/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0890_exp_radius
  have hrNumeric : (492080772669/500000000000 : ℝ) ≤ Real.exp (-66963/4194304 : ℝ) ∧ Real.exp (-66963/4194304 : ℝ) ≤ (984161545339/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492080772669/500000000000 : ℝ) ≤ (radius 8 (66963/524288 : ℝ)) ∧ (radius 8 (66963/524288 : ℝ)) ≤ (984161545339/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66963/524288 : ℝ)) (492080772669/500000000000 : ℝ) (984161545339/1000000000000 : ℝ) (88636974051/500000000000 : ℝ) (177273948109/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66963/524288 : ℝ)) (492080772669/500000000000 : ℝ) (984161545339/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66963/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492080772669/500000000000 : ℝ) (984161545339/1000000000000 : ℝ) (992080772669/1000000000000 : ℝ) (99208077267/100000000000 : ℝ) (496024582389/500000000000 : ℝ) (49602458239/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66963/524288 : ℝ)) 1 (992080772669/1000000000000 : ℝ) (99208077267/100000000000 : ℝ) (496024582389/500000000000 : ℝ) (49602458239/50000000000 : ℝ) (992064968723/1000000000000 : ℝ) (39682598749/40000000000 : ℝ) (992064968597/1000000000000 : ℝ) (4960324843/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66963/524288 : ℝ)) 2 (992064968723/1000000000000 : ℝ) (39682598749/40000000000 : ℝ) (992064968597/1000000000000 : ℝ) (4960324843/5000000000 : ℝ) (49603248433/50000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66963/524288 : ℝ)) 3 (49603248433/50000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66963/524288 : ℝ)) 4 (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66963/524288 : ℝ)) 5 (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66963/524288 : ℝ)) 6 (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66963/524288 : ℝ)) 7 (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66963/524288 : ℝ))) (88636974051/500000000000 : ℝ) (177273948109/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66963/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88636974051/500000000000 : ℝ) (177273948109/1000000000000 : ℝ) (588636974051/1000000000000 : ℝ) (117727394811/200000000000 : ℝ) (26314945559/62500000000 : ℝ) (421039128953/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66963/524288 : ℝ))) 1 (588636974051/1000000000000 : ℝ) (117727394811/200000000000 : ℝ) (26314945559/62500000000 : ℝ) (421039128953/1000000000000 : ℝ) (504838051497/1000000000000 : ℝ) (31552378219/62500000000 : ℝ) (497834509469/1000000000000 : ℝ) (497834509477/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66963/524288 : ℝ))) 2 (504838051497/1000000000000 : ℝ) (31552378219/62500000000 : ℝ) (497834509469/1000000000000 : ℝ) (497834509477/1000000000000 : ℝ) (501336280483/1000000000000 : ℝ) (501336280491/1000000000000 : ℝ) (250662025309/500000000000 : ℝ) (250662025313/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66963/524288 : ℝ))) 3 (501336280483/1000000000000 : ℝ) (501336280491/1000000000000 : ℝ) (250662025309/500000000000 : ℝ) (250662025313/500000000000 : ℝ) (10026603311/20000000000 : ℝ) (501330165559/1000000000000 : ℝ) (501330165513/1000000000000 : ℝ) (250665082761/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66963/524288 : ℝ))) 4 (10026603311/20000000000 : ℝ) (501330165559/1000000000000 : ℝ) (501330165513/1000000000000 : ℝ) (250665082761/500000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66963/524288 : ℝ))) 5 (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66963/524288 : ℝ))) 6 (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66963/524288 : ℝ))) 7 (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66963/524288 : ℝ)) hmem 8 (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66963/524288 : ℝ))) hcmem 8 (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66963/524288 : ℝ)) (992064968659/1000000000000 : ℝ) (992064968663/1000000000000 : ℝ) (501330165531/1000000000000 : ℝ) (501330165541/1000000000000 : ℝ) (396893150853/500000000000 : ℝ) (396893150863/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0890_exp_lower
  have heNumeric : (2054901548533/1000000000000 : ℝ)/4 ≤ Real.exp (-42628251044839/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901548533/1000000000000 : ℝ)/4 ≤ Real.exp ((33481/262144 : ℝ)-(396893150863/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33481/262144 : ℝ) (66963/524288 : ℝ) (396893150863/500000000000 : ℝ) (2054901548533/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0891; no trusted numerical premise.
theorem cover8_leaf0891_exp_radius : (249501576833581463/250000000000000000 : ℝ) ≤ Real.exp ((-16741/1048576 : ℝ)/8) ∧ Real.exp ((-16741/1048576 : ℝ)/8) ≤ (998006307334325853/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16741/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0891_exp_lower : (920113448690548909/1000000000000000000 : ℝ) ≤ Real.exp ((-85256502013437/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256502013437/128000000000000 : ℝ)/8) ≤ (92011344869054891/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256502013437/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0891_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901549757/1000000000000 : ℝ) ≤ 4*Real.exp (66963/524288 : ℝ)*Real.exp (-mu (radius 8 (16741/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901549757/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16741/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0891_exp_radius
  have hrNumeric : (123020163837/125000000000 : ℝ) ≤ Real.exp (-16741/1048576 : ℝ) ∧ Real.exp (-16741/1048576 : ℝ) ≤ (984161310697/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123020163837/125000000000 : ℝ) ≤ (radius 8 (16741/131072 : ℝ)) ∧ (radius 8 (16741/131072 : ℝ)) ≤ (984161310697/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16741/131072 : ℝ)) (123020163837/125000000000 : ℝ) (984161310697/1000000000000 : ℝ) (88637625373/500000000000 : ℝ) (2769925793/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16741/131072 : ℝ)) (123020163837/125000000000 : ℝ) (984161310697/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16741/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123020163837/125000000000 : ℝ) (984161310697/1000000000000 : ℝ) (248020163837/250000000000 : ℝ) (992080655349/1000000000000 : ℝ) (992049046517/1000000000000 : ℝ) (496024523259/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16741/131072 : ℝ)) 1 (248020163837/250000000000 : ℝ) (992080655349/1000000000000 : ℝ) (992049046517/1000000000000 : ℝ) (496024523259/500000000000 : ℝ) (248016212733/250000000000 : ℝ) (496032425467/500000000000 : ℝ) (496032425403/500000000000 : ℝ) (124008106351/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16741/131072 : ℝ)) 2 (248016212733/250000000000 : ℝ) (496032425467/500000000000 : ℝ) (496032425403/500000000000 : ℝ) (124008106351/125000000000 : ℝ) (992064850869/1000000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16741/131072 : ℝ)) 3 (992064850869/1000000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16741/131072 : ℝ)) 4 (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16741/131072 : ℝ)) 5 (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16741/131072 : ℝ)) 6 (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16741/131072 : ℝ)) 7 (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16741/131072 : ℝ))) (88637625373/500000000000 : ℝ) (2769925793/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16741/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88637625373/500000000000 : ℝ) (2769925793/15625000000 : ℝ) (588637625373/1000000000000 : ℝ) (18394925793/31250000000 : ℝ) (10526016897/25000000000 : ℝ) (26315042243/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16741/131072 : ℝ))) 1 (588637625373/1000000000000 : ℝ) (18394925793/31250000000 : ℝ) (10526016897/25000000000 : ℝ) (26315042243/62500000000 : ℝ) (252419575313/500000000000 : ℝ) (63104893829/125000000000 : ℝ) (248917849719/500000000000 : ℝ) (99567139889/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16741/131072 : ℝ))) 2 (252419575313/500000000000 : ℝ) (63104893829/125000000000 : ℝ) (248917849719/500000000000 : ℝ) (99567139889/200000000000 : ℝ) (62667178129/125000000000 : ℝ) (501337425039/1000000000000 : ℝ) (62665649439/125000000000 : ℝ) (501325195519/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16741/131072 : ℝ))) 3 (62667178129/125000000000 : ℝ) (501337425039/1000000000000 : ℝ) (62665649439/125000000000 : ℝ) (501325195519/1000000000000 : ℝ) (7833301723/15625000000 : ℝ) (501331310279/1000000000000 : ℝ) (250665655117/500000000000 : ℝ) (250665655121/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16741/131072 : ℝ))) 4 (7833301723/15625000000 : ℝ) (501331310279/1000000000000 : ℝ) (250665655117/500000000000 : ℝ) (250665655121/500000000000 : ℝ) (501331310253/1000000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16741/131072 : ℝ))) 5 (501331310253/1000000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16741/131072 : ℝ))) 6 (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16741/131072 : ℝ))) 7 (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16741/131072 : ℝ)) hmem 8 (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16741/131072 : ℝ))) hcmem 8 (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16741/131072 : ℝ)) (248016212717/250000000000 : ℝ) (992064850871/1000000000000 : ℝ) (125332827563/250000000000 : ℝ) (501331310261/1000000000000 : ℝ) (396894104231/500000000000 : ℝ) (793788208479/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0891_exp_lower
  have heNumeric : (2054901549757/1000000000000 : ℝ)/4 ≤ Real.exp (-85256502013437/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901549757/1000000000000 : ℝ)/4 ≤ Real.exp ((66963/524288 : ℝ)-(793788208479/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66963/524288 : ℝ) (16741/131072 : ℝ) (793788208479/1000000000000 : ℝ) (2054901549757/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0892; no trusted numerical premise.
theorem cover8_leaf0892_exp_radius : (998006277591420579/1000000000000000000 : ℝ) ≤ Real.exp ((-66965/4194304 : ℝ)/8) ∧ Real.exp ((-66965/4194304 : ℝ)/8) ≤ (49900313879571029/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66965/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0892_exp_lower : (460056724380390171/500000000000000000 : ℝ) ≤ Real.exp ((-21314125483819/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314125483819/32000000000000 : ℝ)/8) ≤ (920113448760780343/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314125483819/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0892_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725387753/250000000000 : ℝ) ≤ 4*Real.exp (16741/131072 : ℝ)*Real.exp (-mu (radius 8 (66965/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725387753/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66965/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0892_exp_radius
  have hrNumeric : (492080538027/500000000000 : ℝ) ≤ Real.exp (-66965/4194304 : ℝ) ∧ Real.exp (-66965/4194304 : ℝ) ≤ (196832215211/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492080538027/500000000000 : ℝ) ≤ (radius 8 (66965/524288 : ℝ)) ∧ (radius 8 (66965/524288 : ℝ)) ≤ (196832215211/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66965/524288 : ℝ)) (492080538027/500000000000 : ℝ) (196832215211/200000000000 : ℝ) (177276553379/1000000000000 : ℝ) (88638276693/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66965/524288 : ℝ)) (492080538027/500000000000 : ℝ) (196832215211/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66965/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492080538027/500000000000 : ℝ) (196832215211/200000000000 : ℝ) (992080538027/1000000000000 : ℝ) (248020134507/250000000000 : ℝ) (1937595563/1953125000 : ℝ) (992048928257/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66965/524288 : ℝ)) 1 (992080538027/1000000000000 : ℝ) (248020134507/250000000000 : ℝ) (1937595563/1953125000 : ℝ) (992048928257/1000000000000 : ℝ) (992064733141/1000000000000 : ℝ) (992064733143/1000000000000 : ℝ) (198412946603/200000000000 : ℝ) (992064733017/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66965/524288 : ℝ)) 2 (992064733141/1000000000000 : ℝ) (992064733143/1000000000000 : ℝ) (198412946603/200000000000 : ℝ) (992064733017/1000000000000 : ℝ) (496032366539/500000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66965/524288 : ℝ)) 3 (496032366539/500000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66965/524288 : ℝ)) 4 (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66965/524288 : ℝ)) 5 (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66965/524288 : ℝ)) 6 (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66965/524288 : ℝ)) 7 (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66965/524288 : ℝ))) (177276553379/1000000000000 : ℝ) (88638276693/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66965/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177276553379/1000000000000 : ℝ) (88638276693/500000000000 : ℝ) (588638276689/1000000000000 : ℝ) (588638276693/1000000000000 : ℝ) (210521111399/500000000000 : ℝ) (421042222807/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66965/524288 : ℝ))) 1 (588638276689/1000000000000 : ℝ) (588638276693/1000000000000 : ℝ) (210521111399/500000000000 : ℝ) (421042222807/1000000000000 : ℝ) (504840249743/1000000000000 : ℝ) (2019360999/4000000000 : ℝ) (497836889393/1000000000000 : ℝ) (497836889401/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66965/524288 : ℝ))) 2 (504840249743/1000000000000 : ℝ) (2019360999/4000000000 : ℝ) (497836889393/1000000000000 : ℝ) (497836889401/1000000000000 : ℝ) (15666830299/31250000000 : ℝ) (62667321197/125000000000 : ℝ) (501326340393/1000000000000 : ℝ) (250663170201/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66965/524288 : ℝ))) 3 (15666830299/31250000000 : ℝ) (62667321197/125000000000 : ℝ) (501326340393/1000000000000 : ℝ) (250663170201/500000000000 : ℝ) (25066622749/50000000000 : ℝ) (501332454989/1000000000000 : ℝ) (501332454943/1000000000000 : ℝ) (62666556869/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66965/524288 : ℝ))) 4 (25066622749/50000000000 : ℝ) (501332454989/1000000000000 : ℝ) (501332454943/1000000000000 : ℝ) (62666556869/125000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66965/524288 : ℝ))) 5 (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66965/524288 : ℝ))) 6 (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66965/524288 : ℝ))) 7 (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66965/524288 : ℝ)) hmem 8 (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66965/524288 : ℝ))) hcmem 8 (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66965/524288 : ℝ)) (992064733077/1000000000000 : ℝ) (24801618327/25000000000 : ℝ) (501332454961/1000000000000 : ℝ) (501332454971/1000000000000 : ℝ) (396895057599/500000000000 : ℝ) (793790115217/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0892_exp_lower
  have heNumeric : (513725387753/250000000000 : ℝ)/4 ≤ Real.exp (-21314125483819/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725387753/250000000000 : ℝ)/4 ≤ Real.exp ((16741/131072 : ℝ)-(793790115217/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16741/131072 : ℝ) (66965/524288 : ℝ) (793790115217/1000000000000 : ℝ) (513725387753/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0893; no trusted numerical premise.
theorem cover8_leaf0893_exp_radius : (998006247848516193/1000000000000000000 : ℝ) ≤ Real.exp ((-33483/2097152 : ℝ)/8) ∧ Real.exp ((-33483/2097152 : ℝ)/8) ≤ (499003123924258097/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33483/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0893_exp_lower : (920113448832161917/1000000000000000000 : ℝ) ≤ Real.exp ((-17051300371167/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051300371167/25600000000000 : ℝ)/8) ≤ (460056724416080959/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051300371167/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0893_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901552287/1000000000000 : ℝ) ≤ 4*Real.exp (66965/524288 : ℝ)*Real.exp (-mu (radius 8 (33483/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901552287/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33483/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0893_exp_radius
  have hrNumeric : (984160841411/1000000000000 : ℝ) ≤ Real.exp (-33483/2097152 : ℝ) ∧ Real.exp (-33483/2097152 : ℝ) ≤ (246040210353/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984160841411/1000000000000 : ℝ) ≤ (radius 8 (33483/262144 : ℝ)) ∧ (radius 8 (33483/262144 : ℝ)) ≤ (246040210353/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33483/262144 : ℝ)) (984160841411/1000000000000 : ℝ) (246040210353/250000000000 : ℝ) (177277856009/1000000000000 : ℝ) (35455571203/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33483/262144 : ℝ)) (984160841411/1000000000000 : ℝ) (246040210353/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33483/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984160841411/1000000000000 : ℝ) (246040210353/250000000000 : ℝ) (198416084141/200000000000 : ℝ) (496040210353/500000000000 : ℝ) (496024404997/500000000000 : ℝ) (198409761999/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33483/262144 : ℝ)) 1 (198416084141/200000000000 : ℝ) (496040210353/500000000000 : ℝ) (496024404997/500000000000 : ℝ) (198409761999/200000000000 : ℝ) (992064615349/1000000000000 : ℝ) (992064615351/1000000000000 : ℝ) (992064615223/1000000000000 : ℝ) (39682584609/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33483/262144 : ℝ)) 2 (992064615349/1000000000000 : ℝ) (992064615351/1000000000000 : ℝ) (992064615223/1000000000000 : ℝ) (39682584609/40000000000 : ℝ) (496032307643/500000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33483/262144 : ℝ)) 3 (496032307643/500000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33483/262144 : ℝ)) 4 (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33483/262144 : ℝ)) 5 (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33483/262144 : ℝ)) 6 (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33483/262144 : ℝ)) 7 (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33483/262144 : ℝ))) (177277856009/1000000000000 : ℝ) (35455571203/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33483/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177277856009/1000000000000 : ℝ) (35455571203/200000000000 : ℝ) (147159732001/250000000000 : ℝ) (73579866001/125000000000 : ℝ) (210521884853/500000000000 : ℝ) (84208753943/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33483/262144 : ℝ))) 1 (147159732001/250000000000 : ℝ) (73579866001/125000000000 : ℝ) (210521884853/500000000000 : ℝ) (84208753943/200000000000 : ℝ) (100968269771/200000000000 : ℝ) (252420674431/500000000000 : ℝ) (497838079341/1000000000000 : ℝ) (497838079349/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33483/262144 : ℝ))) 2 (100968269771/200000000000 : ℝ) (252420674431/500000000000 : ℝ) (497838079341/1000000000000 : ℝ) (497838079349/1000000000000 : ℝ) (250669857049/500000000000 : ℝ) (250669857053/500000000000 : ℝ) (125331871317/250000000000 : ℝ) (501327485277/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33483/262144 : ℝ))) 3 (250669857049/500000000000 : ℝ) (250669857053/500000000000 : ℝ) (125331871317/250000000000 : ℝ) (501327485277/1000000000000 : ℝ) (501333599683/1000000000000 : ℝ) (125333399923/250000000000 : ℝ) (100266719929/200000000000 : ℝ) (100266719931/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33483/262144 : ℝ))) 4 (501333599683/1000000000000 : ℝ) (125333399923/250000000000 : ℝ) (100266719929/200000000000 : ℝ) (100266719931/200000000000 : ℝ) (31333349979/62500000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33483/262144 : ℝ))) 5 (31333349979/62500000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33483/262144 : ℝ))) 6 (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33483/262144 : ℝ))) 7 (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33483/262144 : ℝ)) hmem 8 (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33483/262144 : ℝ))) hcmem 8 (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33483/262144 : ℝ)) (198412923057/200000000000 : ℝ) (124008076911/125000000000 : ℝ) (501333599663/1000000000000 : ℝ) (250666799837/500000000000 : ℝ) (198448005481/250000000000 : ℝ) (158758404389/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0893_exp_lower
  have heNumeric : (2054901552287/1000000000000 : ℝ)/4 ≤ Real.exp (-17051300371167/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901552287/1000000000000 : ℝ)/4 ≤ Real.exp ((66965/524288 : ℝ)-(158758404389/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66965/524288 : ℝ) (33483/262144 : ℝ) (158758404389/200000000000 : ℝ) (2054901552287/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0894; no trusted numerical premise.
theorem cover8_leaf0894_exp_radius : (998006218105612693/1000000000000000000 : ℝ) ≤ Real.exp ((-66967/4194304 : ℝ)/8) ∧ Real.exp ((-66967/4194304 : ℝ)/8) ≤ (499003109052806347/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66967/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0894_exp_lower : (920113448906993917/1000000000000000000 : ℝ) ≤ Real.exp ((-42628250886277/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628250886277/64000000000000 : ℝ)/8) ≤ (460056724453496959/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628250886277/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0894_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862694203/125000000000 : ℝ) ≤ 4*Real.exp (33483/262144 : ℝ)*Real.exp (-mu (radius 8 (66967/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862694203/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66967/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0894_exp_radius
  have hrNumeric : (984160606769/1000000000000 : ℝ) ≤ Real.exp (-66967/4194304 : ℝ) ∧ Real.exp (-66967/4194304 : ℝ) ≤ (98416060677/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984160606769/1000000000000 : ℝ) ≤ (radius 8 (66967/524288 : ℝ)) ∧ (radius 8 (66967/524288 : ℝ)) ≤ (98416060677/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66967/524288 : ℝ)) (984160606769/1000000000000 : ℝ) (98416060677/100000000000 : ℝ) (177279158623/1000000000000 : ℝ) (177279158629/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66967/524288 : ℝ)) (984160606769/1000000000000 : ℝ) (98416060677/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66967/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984160606769/1000000000000 : ℝ) (98416060677/100000000000 : ℝ) (124010037923/125000000000 : ℝ) (198416060677/200000000000 : ℝ) (248012172933/250000000000 : ℝ) (496024345867/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66967/524288 : ℝ)) 1 (124010037923/125000000000 : ℝ) (198416060677/200000000000 : ℝ) (248012172933/250000000000 : ℝ) (496024345867/500000000000 : ℝ) (496032248779/500000000000 : ℝ) (24801612439/25000000000 : ℝ) (124008062179/125000000000 : ℝ) (496032248717/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66967/524288 : ℝ)) 2 (496032248779/500000000000 : ℝ) (24801612439/25000000000 : ℝ) (124008062179/125000000000 : ℝ) (496032248717/500000000000 : ℝ) (198412899499/200000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66967/524288 : ℝ)) 3 (198412899499/200000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66967/524288 : ℝ)) 4 (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66967/524288 : ℝ)) 5 (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66967/524288 : ℝ)) 6 (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66967/524288 : ℝ)) 7 (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66967/524288 : ℝ))) (177279158623/1000000000000 : ℝ) (177279158629/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66967/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177279158623/1000000000000 : ℝ) (177279158629/1000000000000 : ℝ) (588639579311/1000000000000 : ℝ) (117727915863/200000000000 : ℝ) (42104531659/100000000000 : ℝ) (210522658299/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66967/524288 : ℝ))) 1 (588639579311/1000000000000 : ℝ) (117727915863/200000000000 : ℝ) (42104531659/100000000000 : ℝ) (210522658299/500000000000 : ℝ) (10096848959/20000000000 : ℝ) (504842447957/1000000000000 : ℝ) (497839269271/1000000000000 : ℝ) (248919634639/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66967/524288 : ℝ))) 2 (10096848959/20000000000 : ℝ) (504842447957/1000000000000 : ℝ) (497839269271/1000000000000 : ℝ) (248919634639/500000000000 : ℝ) (50134085861/100000000000 : ℝ) (250670429309/500000000000 : ℝ) (250664315063/500000000000 : ℝ) (250664315067/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66967/524288 : ℝ))) 3 (50134085861/100000000000 : ℝ) (250670429309/500000000000 : ℝ) (250664315063/500000000000 : ℝ) (250664315067/500000000000 : ℝ) (31333421523/62500000000 : ℝ) (62666843047/125000000000 : ℝ) (50133474433/100000000000 : ℝ) (501334744339/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66967/524288 : ℝ))) 4 (31333421523/62500000000 : ℝ) (62666843047/125000000000 : ℝ) (50133474433/100000000000 : ℝ) (501334744339/1000000000000 : ℝ) (501334744349/1000000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66967/524288 : ℝ))) 5 (501334744349/1000000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66967/524288 : ℝ))) 6 (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66967/524288 : ℝ))) 7 (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66967/524288 : ℝ)) hmem 8 (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66967/524288 : ℝ))) hcmem 8 (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66967/524288 : ℝ)) (496032248747/500000000000 : ℝ) (992064497497/1000000000000 : ℝ) (125333686087/250000000000 : ℝ) (250667372179/500000000000 : ℝ) (793793928623/1000000000000 : ℝ) (793793928643/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0894_exp_lower
  have heNumeric : (256862694203/125000000000 : ℝ)/4 ≤ Real.exp (-42628250886277/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862694203/125000000000 : ℝ)/4 ≤ Real.exp ((33483/262144 : ℝ)-(793793928643/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33483/262144 : ℝ) (66967/524288 : ℝ) (793793928643/1000000000000 : ℝ) (256862694203/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0895; no trusted numerical premise.
theorem cover8_leaf0895_exp_radius : (998006188362710079/1000000000000000000 : ℝ) ≤ Real.exp ((-8371/524288 : ℝ)/8) ∧ Real.exp ((-8371/524288 : ℝ)/8) ≤ (3118769338633469/3125000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8371/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0895_exp_lower : (230028362245974043/250000000000000000 : ℝ) ≤ Real.exp ((-85256501686969/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256501686969/128000000000000 : ℝ)/8) ≤ (920113448983896173/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256501686969/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0895_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450777499/500000000000 : ℝ) ≤ 4*Real.exp (66967/524288 : ℝ)*Real.exp (-mu (radius 8 (8371/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450777499/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8371/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0895_exp_radius
  have hrNumeric : (984160372127/1000000000000 : ℝ) ≤ Real.exp (-8371/524288 : ℝ) ∧ Real.exp (-8371/524288 : ℝ) ≤ (30755011629/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984160372127/1000000000000 : ℝ) ≤ (radius 8 (8371/65536 : ℝ)) ∧ (radius 8 (8371/65536 : ℝ)) ≤ (30755011629/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8371/65536 : ℝ)) (984160372127/1000000000000 : ℝ) (30755011629/31250000000 : ℝ) (177280461227/1000000000000 : ℝ) (177280461233/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8371/65536 : ℝ)) (984160372127/1000000000000 : ℝ) (30755011629/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8371/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984160372127/1000000000000 : ℝ) (30755011629/31250000000 : ℝ) (992080186063/1000000000000 : ℝ) (62005011629/62500000000 : ℝ) (992048573471/1000000000000 : ℝ) (992048573473/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8371/65536 : ℝ)) 1 (992080186063/1000000000000 : ℝ) (62005011629/62500000000 : ℝ) (992048573471/1000000000000 : ℝ) (992048573473/1000000000000 : ℝ) (992064379767/1000000000000 : ℝ) (992064379769/1000000000000 : ℝ) (992064379641/1000000000000 : ℝ) (992064379643/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8371/65536 : ℝ)) 2 (992064379767/1000000000000 : ℝ) (992064379769/1000000000000 : ℝ) (992064379641/1000000000000 : ℝ) (992064379643/1000000000000 : ℝ) (124008047463/125000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8371/65536 : ℝ)) 3 (124008047463/125000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8371/65536 : ℝ)) 4 (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8371/65536 : ℝ)) 5 (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8371/65536 : ℝ)) 6 (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8371/65536 : ℝ)) 7 (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8371/65536 : ℝ))) (177280461227/1000000000000 : ℝ) (177280461233/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8371/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177280461227/1000000000000 : ℝ) (177280461233/1000000000000 : ℝ) (588640230613/1000000000000 : ℝ) (588640230617/1000000000000 : ℝ) (421046863457/1000000000000 : ℝ) (84209372693/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8371/65536 : ℝ))) 1 (588640230613/1000000000000 : ℝ) (588640230617/1000000000000 : ℝ) (421046863457/1000000000000 : ℝ) (84209372693/200000000000 : ℝ) (100968709407/200000000000 : ℝ) (504843547041/1000000000000 : ℝ) (497840459187/1000000000000 : ℝ) (99568091839/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8371/65536 : ℝ))) 2 (100968709407/200000000000 : ℝ) (504843547041/1000000000000 : ℝ) (497840459187/1000000000000 : ℝ) (99568091839/200000000000 : ℝ) (501342003111/1000000000000 : ℝ) (250671001559/500000000000 : ℝ) (125332443743/250000000000 : ℝ) (25066488749/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8371/65536 : ℝ))) 3 (501342003111/1000000000000 : ℝ) (250671001559/500000000000 : ℝ) (125332443743/250000000000 : ℝ) (25066488749/50000000000 : ℝ) (501335889041/1000000000000 : ℝ) (501335889049/1000000000000 : ℝ) (125333972251/250000000000 : ℝ) (125333972253/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8371/65536 : ℝ))) 4 (501335889041/1000000000000 : ℝ) (501335889049/1000000000000 : ℝ) (125333972251/250000000000 : ℝ) (125333972253/250000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8371/65536 : ℝ))) 5 (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8371/65536 : ℝ))) 6 (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8371/65536 : ℝ))) 7 (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8371/65536 : ℝ)) hmem 8 (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8371/65536 : ℝ))) hcmem 8 (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8371/65536 : ℝ)) (992064379703/1000000000000 : ℝ) (496032189853/500000000000 : ℝ) (250667944511/500000000000 : ℝ) (501335889031/1000000000000 : ℝ) (396897917653/500000000000 : ℝ) (793795835323/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0895_exp_lower
  have heNumeric : (1027450777499/500000000000 : ℝ)/4 ≤ Real.exp (-85256501686969/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450777499/500000000000 : ℝ)/4 ≤ Real.exp ((66967/524288 : ℝ)-(793795835323/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66967/524288 : ℝ) (8371/65536 : ℝ) (793795835323/1000000000000 : ℝ) (1027450777499/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0896; no trusted numerical premise.
theorem cover8_leaf0896_exp_radius : (31187692456869011/31250000000000000 : ℝ) ≤ Real.exp ((-66969/4194304 : ℝ)/8) ∧ Real.exp ((-66969/4194304 : ℝ)/8) ≤ (998006158619808353/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66969/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0896_exp_lower : (920113449062983697/1000000000000000000 : ℝ) ≤ Real.exp ((-10657062699869/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657062699869/16000000000000 : ℝ)/8) ≤ (460056724531491849/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657062699869/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0896_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901556411/1000000000000 : ℝ) ≤ 4*Real.exp (8371/65536 : ℝ)*Real.exp (-mu (radius 8 (66969/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901556411/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66969/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0896_exp_radius
  have hrNumeric : (196832027497/200000000000 : ℝ) ≤ Real.exp (-66969/4194304 : ℝ) ∧ Real.exp (-66969/4194304 : ℝ) ≤ (492080068743/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196832027497/200000000000 : ℝ) ≤ (radius 8 (66969/524288 : ℝ)) ∧ (radius 8 (66969/524288 : ℝ)) ≤ (492080068743/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66969/524288 : ℝ)) (196832027497/200000000000 : ℝ) (492080068743/500000000000 : ℝ) (177281763821/1000000000000 : ℝ) (177281763827/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66969/524288 : ℝ)) (196832027497/200000000000 : ℝ) (492080068743/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66969/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196832027497/200000000000 : ℝ) (492080068743/500000000000 : ℝ) (496040034371/500000000000 : ℝ) (992080068743/1000000000000 : ℝ) (99204845521/100000000000 : ℝ) (992048455211/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66969/524288 : ℝ)) 1 (496040034371/500000000000 : ℝ) (992080068743/1000000000000 : ℝ) (99204845521/100000000000 : ℝ) (992048455211/1000000000000 : ℝ) (124008032747/125000000000 : ℝ) (992064261977/1000000000000 : ℝ) (19841285237/20000000000 : ℝ) (248016065463/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66969/524288 : ℝ)) 2 (124008032747/125000000000 : ℝ) (992064261977/1000000000000 : ℝ) (19841285237/20000000000 : ℝ) (248016065463/250000000000 : ℝ) (992064261913/1000000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66969/524288 : ℝ)) 3 (992064261913/1000000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66969/524288 : ℝ)) 4 (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66969/524288 : ℝ)) 5 (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66969/524288 : ℝ)) 6 (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66969/524288 : ℝ)) 7 (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66969/524288 : ℝ))) (177281763821/1000000000000 : ℝ) (177281763827/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66969/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177281763821/1000000000000 : ℝ) (177281763827/1000000000000 : ℝ) (58864088191/100000000000 : ℝ) (294320440957/500000000000 : ℝ) (84209682061/200000000000 : ℝ) (421048410313/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66969/524288 : ℝ))) 1 (58864088191/100000000000 : ℝ) (294320440957/500000000000 : ℝ) (84209682061/200000000000 : ℝ) (421048410313/1000000000000 : ℝ) (504844646107/1000000000000 : ℝ) (252422323057/500000000000 : ℝ) (49784164909/100000000000 : ℝ) (497841649097/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66969/524288 : ℝ))) 2 (504844646107/1000000000000 : ℝ) (252422323057/500000000000 : ℝ) (49784164909/100000000000 : ℝ) (497841649097/1000000000000 : ℝ) (250671573799/500000000000 : ℝ) (250671573803/500000000000 : ℝ) (125332729951/250000000000 : ℝ) (125332729953/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66969/524288 : ℝ))) 3 (250671573799/500000000000 : ℝ) (250671573803/500000000000 : ℝ) (125332729951/250000000000 : ℝ) (125332729953/250000000000 : ℝ) (501337033701/1000000000000 : ℝ) (501337033709/1000000000000 : ℝ) (501337033663/1000000000000 : ℝ) (62667129209/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66969/524288 : ℝ))) 4 (501337033701/1000000000000 : ℝ) (501337033709/1000000000000 : ℝ) (501337033663/1000000000000 : ℝ) (62667129209/125000000000 : ℝ) (250668516841/500000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66969/524288 : ℝ))) 5 (250668516841/500000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66969/524288 : ℝ))) 6 (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66969/524288 : ℝ))) 7 (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66969/524288 : ℝ)) hmem 8 (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66969/524288 : ℝ))) hcmem 8 (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66969/524288 : ℝ)) (124008032739/125000000000 : ℝ) (198412852383/200000000000 : ℝ) (501337033681/1000000000000 : ℝ) (501337033691/1000000000000 : ℝ) (158759548393/200000000000 : ℝ) (24806179437/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0896_exp_lower
  have heNumeric : (2054901556411/1000000000000 : ℝ)/4 ≤ Real.exp (-10657062699869/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901556411/1000000000000 : ℝ)/4 ≤ Real.exp ((8371/65536 : ℝ)-(24806179437/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8371/65536 : ℝ) (66969/524288 : ℝ) (24806179437/31250000000 : ℝ) (2054901556411/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0897; no trusted numerical premise.
theorem cover8_leaf0897_exp_radius : (998006128876907511/1000000000000000000 : ℝ) ≤ Real.exp ((-33485/2097152 : ℝ)/8) ∧ Real.exp ((-33485/2097152 : ℝ)/8) ≤ (124750766109613439/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33485/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0897_exp_lower : (920113449144026463/1000000000000000000 : ℝ) ≤ Real.exp ((-85256501508759/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256501508759/128000000000000 : ℝ)/8) ≤ (28753545285750827/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256501508759/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0897_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901557859/1000000000000 : ℝ) ≤ 4*Real.exp (66969/524288 : ℝ)*Real.exp (-mu (radius 8 (33485/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901557859/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33485/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0897_exp_radius
  have hrNumeric : (984159902843/1000000000000 : ℝ) ≤ Real.exp (-33485/2097152 : ℝ) ∧ Real.exp (-33485/2097152 : ℝ) ≤ (246039975711/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984159902843/1000000000000 : ℝ) ≤ (radius 8 (33485/262144 : ℝ)) ∧ (radius 8 (33485/262144 : ℝ)) ≤ (246039975711/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33485/262144 : ℝ)) (984159902843/1000000000000 : ℝ) (246039975711/250000000000 : ℝ) (35456613281/200000000000 : ℝ) (177283066411/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33485/262144 : ℝ)) (984159902843/1000000000000 : ℝ) (246039975711/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33485/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984159902843/1000000000000 : ℝ) (246039975711/250000000000 : ℝ) (992079951421/1000000000000 : ℝ) (496039975711/500000000000 : ℝ) (248012084237/250000000000 : ℝ) (19840966739/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33485/262144 : ℝ)) 1 (992079951421/1000000000000 : ℝ) (496039975711/500000000000 : ℝ) (248012084237/250000000000 : ℝ) (19840966739/20000000000 : ℝ) (124008018023/125000000000 : ℝ) (496032072093/500000000000 : ℝ) (496032072029/500000000000 : ℝ) (992064144061/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33485/262144 : ℝ)) 2 (124008018023/125000000000 : ℝ) (496032072093/500000000000 : ℝ) (496032072029/500000000000 : ℝ) (992064144061/1000000000000 : ℝ) (992064144121/1000000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33485/262144 : ℝ)) 3 (992064144121/1000000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33485/262144 : ℝ)) 4 (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33485/262144 : ℝ)) 5 (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33485/262144 : ℝ)) 6 (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33485/262144 : ℝ)) 7 (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33485/262144 : ℝ))) (35456613281/200000000000 : ℝ) (177283066411/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33485/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35456613281/200000000000 : ℝ) (177283066411/1000000000000 : ℝ) (294320766601/500000000000 : ℝ) (294320766603/500000000000 : ℝ) (26315622321/62500000000 : ℝ) (84209991429/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33485/262144 : ℝ))) 1 (294320766601/500000000000 : ℝ) (294320766603/500000000000 : ℝ) (26315622321/62500000000 : ℝ) (84209991429/200000000000 : ℝ) (504845745169/1000000000000 : ℝ) (63105718147/125000000000 : ℝ) (497842838979/1000000000000 : ℝ) (497842838987/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33485/262144 : ℝ))) 2 (504845745169/1000000000000 : ℝ) (63105718147/125000000000 : ℝ) (497842838979/1000000000000 : ℝ) (497842838987/1000000000000 : ℝ) (250672146037/500000000000 : ℝ) (250672146041/500000000000 : ℝ) (4010656517/8000000000 : ℝ) (501332064633/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33485/262144 : ℝ))) 3 (250672146037/500000000000 : ℝ) (250672146041/500000000000 : ℝ) (4010656517/8000000000 : ℝ) (501332064633/1000000000000 : ℝ) (501338178349/1000000000000 : ℝ) (250669089179/500000000000 : ℝ) (62667272289/125000000000 : ℝ) (501338178321/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33485/262144 : ℝ))) 4 (501338178349/1000000000000 : ℝ) (250669089179/500000000000 : ℝ) (62667272289/125000000000 : ℝ) (501338178321/1000000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33485/262144 : ℝ))) 5 (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33485/262144 : ℝ))) 6 (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33485/262144 : ℝ))) 7 (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33485/262144 : ℝ)) hmem 8 (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33485/262144 : ℝ))) hcmem 8 (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33485/262144 : ℝ)) (24801603603/25000000000 : ℝ) (248016036031/250000000000 : ℝ) (50133817833/100000000000 : ℝ) (25066908917/50000000000 : ℝ) (24806239019/31250000000 : ℝ) (198449912157/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0897_exp_lower
  have heNumeric : (2054901557859/1000000000000 : ℝ)/4 ≤ Real.exp (-85256501508759/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901557859/1000000000000 : ℝ)/4 ≤ Real.exp ((66969/524288 : ℝ)-(198449912157/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66969/524288 : ℝ) (33485/262144 : ℝ) (198449912157/250000000000 : ℝ) (2054901557859/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0898; no trusted numerical premise.
theorem cover8_leaf0898_exp_radius : (249501524783501889/250000000000000000 : ℝ) ≤ Real.exp ((-66971/4194304 : ℝ)/8) ∧ Real.exp ((-66971/4194304 : ℝ)/8) ≤ (998006099134007557/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66971/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0898_exp_lower : (920113449227599541/1000000000000000000 : ℝ) ≤ Real.exp ((-341026005663/512000000000 : ℝ)/8) ∧ Real.exp ((-341026005663/512000000000 : ℝ)/8) ≤ (460056724613799771/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341026005663/512000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0898_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862694919/125000000000 : ℝ) ≤ 4*Real.exp (33485/262144 : ℝ)*Real.exp (-mu (radius 8 (66971/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862694919/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66971/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0898_exp_radius
  have hrNumeric : (984159668201/1000000000000 : ℝ) ≤ Real.exp (-66971/4194304 : ℝ) ∧ Real.exp (-66971/4194304 : ℝ) ≤ (492079834101/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984159668201/1000000000000 : ℝ) ≤ (radius 8 (66971/524288 : ℝ)) ∧ (radius 8 (66971/524288 : ℝ)) ≤ (492079834101/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66971/524288 : ℝ)) (984159668201/1000000000000 : ℝ) (492079834101/500000000000 : ℝ) (177284368979/1000000000000 : ℝ) (88642184493/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66971/524288 : ℝ)) (984159668201/1000000000000 : ℝ) (492079834101/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66971/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984159668201/1000000000000 : ℝ) (492079834101/500000000000 : ℝ) (9920798341/10000000000 : ℝ) (992079834101/1000000000000 : ℝ) (992048218687/1000000000000 : ℝ) (15500753417/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66971/524288 : ℝ)) 1 (9920798341/10000000000 : ℝ) (992079834101/1000000000000 : ℝ) (992048218687/1000000000000 : ℝ) (15500753417/15625000000 : ℝ) (992064026393/1000000000000 : ℝ) (198412805279/200000000000 : ℝ) (992064026267/1000000000000 : ℝ) (992064026269/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66971/524288 : ℝ)) 2 (992064026393/1000000000000 : ℝ) (198412805279/200000000000 : ℝ) (992064026267/1000000000000 : ℝ) (992064026269/1000000000000 : ℝ) (99206402633/100000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66971/524288 : ℝ)) 3 (99206402633/100000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66971/524288 : ℝ)) 4 (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66971/524288 : ℝ)) 5 (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66971/524288 : ℝ)) 6 (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66971/524288 : ℝ)) 7 (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66971/524288 : ℝ))) (177284368979/1000000000000 : ℝ) (88642184493/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66971/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177284368979/1000000000000 : ℝ) (88642184493/500000000000 : ℝ) (588642184489/1000000000000 : ℝ) (588642184493/1000000000000 : ℝ) (8421030079/20000000000 : ℝ) (421051503959/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66971/524288 : ℝ))) 1 (588642184489/1000000000000 : ℝ) (588642184493/1000000000000 : ℝ) (8421030079/20000000000 : ℝ) (421051503959/1000000000000 : ℝ) (504846844219/1000000000000 : ℝ) (252423422113/500000000000 : ℝ) (99568805771/200000000000 : ℝ) (497844028863/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66971/524288 : ℝ))) 2 (504846844219/1000000000000 : ℝ) (252423422113/500000000000 : ℝ) (99568805771/200000000000 : ℝ) (497844028863/1000000000000 : ℝ) (501345436537/1000000000000 : ℝ) (100269087309/200000000000 : ℝ) (501333209433/1000000000000 : ℝ) (501333209441/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66971/524288 : ℝ))) 3 (501345436537/1000000000000 : ℝ) (100269087309/200000000000 : ℝ) (501333209433/1000000000000 : ℝ) (501333209441/1000000000000 : ℝ) (100267864597/200000000000 : ℝ) (501339322993/1000000000000 : ℝ) (501339322947/1000000000000 : ℝ) (125334830739/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66971/524288 : ℝ))) 4 (100267864597/200000000000 : ℝ) (501339322993/1000000000000 : ℝ) (501339322947/1000000000000 : ℝ) (125334830739/250000000000 : ℝ) (250669661483/500000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66971/524288 : ℝ))) 5 (250669661483/500000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66971/524288 : ℝ))) 6 (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66971/524288 : ℝ))) 7 (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66971/524288 : ℝ)) hmem 8 (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66971/524288 : ℝ))) hcmem 8 (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66971/524288 : ℝ)) (992064026329/1000000000000 : ℝ) (248016006583/250000000000 : ℝ) (100267864593/200000000000 : ℝ) (20053572919/40000000000 : ℝ) (793801555231/1000000000000 : ℝ) (3175206221/4000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0898_exp_lower
  have heNumeric : (256862694919/125000000000 : ℝ)/4 ≤ Real.exp (-341026005663/512000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862694919/125000000000 : ℝ)/4 ≤ Real.exp ((33485/262144 : ℝ)-(3175206221/4000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33485/262144 : ℝ) (66971/524288 : ℝ) (3175206221/4000000000 : ℝ) (256862694919/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0899; no trusted numerical premise.
theorem cover8_leaf0899_exp_radius : (124750758673888561/125000000000000000 : ℝ) ≤ Real.exp ((-16743/1048576 : ℝ)/8) ∧ Real.exp ((-16743/1048576 : ℝ)/8) ≤ (998006069391108489/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16743/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0899_exp_lower : (46005672465656393/50000000000000000 : ℝ) ≤ Real.exp ((-17051300264113/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051300264113/25600000000000 : ℝ)/8) ≤ (920113449313127861/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051300264113/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0899_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686269511/12500000000 : ℝ) ≤ 4*Real.exp (66971/524288 : ℝ)*Real.exp (-mu (radius 8 (16743/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (25686269511/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16743/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0899_exp_radius
  have hrNumeric : (984159433559/1000000000000 : ℝ) ≤ Real.exp (-16743/1048576 : ℝ) ∧ Real.exp (-16743/1048576 : ℝ) ≤ (24603985839/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984159433559/1000000000000 : ℝ) ≤ (radius 8 (16743/131072 : ℝ)) ∧ (radius 8 (16743/131072 : ℝ)) ≤ (24603985839/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16743/131072 : ℝ)) (984159433559/1000000000000 : ℝ) (24603985839/25000000000 : ℝ) (22160708943/125000000000 : ℝ) (3545713431/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16743/131072 : ℝ)) (984159433559/1000000000000 : ℝ) (24603985839/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16743/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984159433559/1000000000000 : ℝ) (24603985839/25000000000 : ℝ) (992079716779/1000000000000 : ℝ) (49603985839/50000000000 : ℝ) (496024050213/500000000000 : ℝ) (992048100427/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16743/131072 : ℝ)) 1 (992079716779/1000000000000 : ℝ) (49603985839/50000000000 : ℝ) (496024050213/500000000000 : ℝ) (992048100427/1000000000000 : ℝ) (496031954301/500000000000 : ℝ) (248015977151/250000000000 : ℝ) (248015977119/250000000000 : ℝ) (496031954239/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16743/131072 : ℝ)) 2 (496031954301/500000000000 : ℝ) (248015977151/250000000000 : ℝ) (248015977119/250000000000 : ℝ) (496031954239/500000000000 : ℝ) (992063908539/1000000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16743/131072 : ℝ)) 3 (992063908539/1000000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16743/131072 : ℝ)) 4 (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16743/131072 : ℝ)) 5 (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16743/131072 : ℝ)) 6 (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16743/131072 : ℝ)) 7 (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16743/131072 : ℝ))) (22160708943/125000000000 : ℝ) (3545713431/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16743/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22160708943/125000000000 : ℝ) (3545713431/20000000000 : ℝ) (147160708943/250000000000 : ℝ) (23545713431/40000000000 : ℝ) (421053050747/1000000000000 : ℝ) (84210610151/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16743/131072 : ℝ))) 1 (147160708943/250000000000 : ℝ) (23545713431/40000000000 : ℝ) (421053050747/1000000000000 : ℝ) (84210610151/200000000000 : ℝ) (504847943259/1000000000000 : ℝ) (100969588653/200000000000 : ℝ) (497845218719/1000000000000 : ℝ) (248922609363/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16743/131072 : ℝ))) 2 (504847943259/1000000000000 : ℝ) (100969588653/200000000000 : ℝ) (497845218719/1000000000000 : ℝ) (248922609363/500000000000 : ℝ) (501346580989/1000000000000 : ℝ) (125336645249/250000000000 : ℝ) (50133435423/100000000000 : ℝ) (501334354237/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16743/131072 : ℝ))) 3 (501346580989/1000000000000 : ℝ) (125336645249/250000000000 : ℝ) (50133435423/100000000000 : ℝ) (501334354237/1000000000000 : ℝ) (501340467609/1000000000000 : ℝ) (501340467617/1000000000000 : ℝ) (125335116893/250000000000 : ℝ) (25067023379/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16743/131072 : ℝ))) 4 (501340467609/1000000000000 : ℝ) (501340467617/1000000000000 : ℝ) (125335116893/250000000000 : ℝ) (25067023379/50000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16743/131072 : ℝ))) 5 (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16743/131072 : ℝ))) 6 (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16743/131072 : ℝ))) 7 (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16743/131072 : ℝ)) hmem 8 (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16743/131072 : ℝ))) hcmem 8 (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16743/131072 : ℝ)) (496031954269/500000000000 : ℝ) (992063908541/1000000000000 : ℝ) (50134046759/100000000000 : ℝ) (501340467599/1000000000000 : ℝ) (793803461837/1000000000000 : ℝ) (158760692371/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0899_exp_lower
  have heNumeric : (25686269511/12500000000 : ℝ)/4 ≤ Real.exp (-17051300264113/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686269511/12500000000 : ℝ)/4 ≤ Real.exp ((66971/524288 : ℝ)-(158760692371/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66971/524288 : ℝ) (16743/131072 : ℝ) (158760692371/200000000000 : ℝ) (25686269511/12500000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0875_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0875_certificate
#check SmaleRate.Proofs.cover8_leaf0876_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0876_certificate
#check SmaleRate.Proofs.cover8_leaf0877_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0877_certificate
#check SmaleRate.Proofs.cover8_leaf0878_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0878_certificate
#check SmaleRate.Proofs.cover8_leaf0879_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0879_certificate
#check SmaleRate.Proofs.cover8_leaf0880_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0880_certificate
#check SmaleRate.Proofs.cover8_leaf0881_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0881_certificate
#check SmaleRate.Proofs.cover8_leaf0882_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0882_certificate
#check SmaleRate.Proofs.cover8_leaf0883_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0883_certificate
#check SmaleRate.Proofs.cover8_leaf0884_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0884_certificate
#check SmaleRate.Proofs.cover8_leaf0885_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0885_certificate
#check SmaleRate.Proofs.cover8_leaf0886_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0886_certificate
#check SmaleRate.Proofs.cover8_leaf0887_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0887_certificate
#check SmaleRate.Proofs.cover8_leaf0888_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0888_certificate
#check SmaleRate.Proofs.cover8_leaf0889_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0889_certificate
#check SmaleRate.Proofs.cover8_leaf0890_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0890_certificate
#check SmaleRate.Proofs.cover8_leaf0891_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0891_certificate
#check SmaleRate.Proofs.cover8_leaf0892_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0892_certificate
#check SmaleRate.Proofs.cover8_leaf0893_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0893_certificate
#check SmaleRate.Proofs.cover8_leaf0894_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0894_certificate
#check SmaleRate.Proofs.cover8_leaf0895_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0895_certificate
#check SmaleRate.Proofs.cover8_leaf0896_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0896_certificate
#check SmaleRate.Proofs.cover8_leaf0897_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0897_certificate
#check SmaleRate.Proofs.cover8_leaf0898_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0898_certificate
#check SmaleRate.Proofs.cover8_leaf0899_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0899_certificate
