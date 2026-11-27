/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0275; no trusted numerical premise.
theorem cover7_leaf0275_exp_radius : (12469771074925139/12500000000000000 : ℝ) ≤ Real.exp ((-4443/229376 : ℝ)/8) ∧ Real.exp ((-4443/229376 : ℝ)/8) ≤ (997581685994011121/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4443/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0275_exp_lower : (918089135583237521/1000000000000000000 : ℝ) ≤ Real.exp ((-10938981822731/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938981822731/16000000000000 : ℝ)/8) ≤ (459044567791618761/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938981822731/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0275_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504752855817/250000000000 : ℝ) ≤ 4*Real.exp (8885/65536 : ℝ)*Real.exp (-mu (radius 7 (4443/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504752855817/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4443/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0275_exp_radius
  have hrNumeric : (980816449133/1000000000000 : ℝ) ≤ Real.exp (-4443/229376 : ℝ) ∧ Real.exp (-4443/229376 : ℝ) ≤ (490408224567/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980816449133/1000000000000 : ℝ) ≤ (radius 7 (4443/32768 : ℝ)) ∧ (radius 7 (4443/32768 : ℝ)) ≤ (490408224567/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4443/32768 : ℝ)) (980816449133/1000000000000 : ℝ) (490408224567/500000000000 : ℝ) (194933560753/1000000000000 : ℝ) (194933560759/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4443/32768 : ℝ)) (980816449133/1000000000000 : ℝ) (490408224567/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4443/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980816449133/1000000000000 : ℝ) (490408224567/500000000000 : ℝ) (495204112283/500000000000 : ℝ) (990408224567/1000000000000 : ℝ) (495180888447/500000000000 : ℝ) (198072355379/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4443/32768 : ℝ)) 1 (495204112283/500000000000 : ℝ) (990408224567/1000000000000 : ℝ) (495180888447/500000000000 : ℝ) (198072355379/200000000000 : ℝ) (99038500073/100000000000 : ℝ) (990385000731/1000000000000 : ℝ) (990385000457/1000000000000 : ℝ) (990385000459/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4443/32768 : ℝ)) 2 (99038500073/100000000000 : ℝ) (990385000731/1000000000000 : ℝ) (990385000457/1000000000000 : ℝ) (990385000459/1000000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4443/32768 : ℝ)) 3 (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4443/32768 : ℝ)) 4 (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4443/32768 : ℝ)) 5 (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4443/32768 : ℝ)) 6 (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4443/32768 : ℝ)) 7 (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4443/32768 : ℝ))) (194933560753/1000000000000 : ℝ) (194933560759/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4443/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194933560753/1000000000000 : ℝ) (194933560759/1000000000000 : ℝ) (74683347547/125000000000 : ℝ) (29873339019/50000000000 : ℝ) (441512809273/1000000000000 : ℝ) (441512809281/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4443/32768 : ℝ))) 1 (74683347547/125000000000 : ℝ) (29873339019/50000000000 : ℝ) (441512809273/1000000000000 : ℝ) (441512809281/1000000000000 : ℝ) (64936224353/125000000000 : ℝ) (519489794831/1000000000000 : ℝ) (513604163389/1000000000000 : ℝ) (128401040849/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4443/32768 : ℝ))) 2 (64936224353/125000000000 : ℝ) (519489794831/1000000000000 : ℝ) (513604163389/1000000000000 : ℝ) (128401040849/250000000000 : ℝ) (258273489553/500000000000 : ℝ) (258273489557/500000000000 : ℝ) (129134649073/250000000000 : ℝ) (5165385963/10000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4443/32768 : ℝ))) 3 (258273489553/500000000000 : ℝ) (258273489557/500000000000 : ℝ) (129134649073/250000000000 : ℝ) (5165385963/10000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787707/1000000000000 : ℝ) (516542787681/1000000000000 : ℝ) (51654278769/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4443/32768 : ℝ))) 4 (516542787699/1000000000000 : ℝ) (516542787707/1000000000000 : ℝ) (516542787681/1000000000000 : ℝ) (51654278769/100000000000 : ℝ) (51654278769/100000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4443/32768 : ℝ))) 5 (51654278769/100000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4443/32768 : ℝ))) 6 (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4443/32768 : ℝ))) 7 (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4443/32768 : ℝ)) hmem 8 (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4443/32768 : ℝ))) hcmem 8 (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4443/32768 : ℝ)) (990385000593/1000000000000 : ℝ) (198077000119/200000000000 : ℝ) (516542787689/1000000000000 : ℝ) (516542787699/1000000000000 : ℝ) (409630352361/500000000000 : ℝ) (819260704741/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0275_exp_lower
  have heNumeric : (504752855817/250000000000 : ℝ)/4 ≤ Real.exp (-10938981822731/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504752855817/250000000000 : ℝ)/4 ≤ Real.exp ((8885/65536 : ℝ)-(819260704741/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8885/65536 : ℝ) (4443/32768 : ℝ) (819260704741/1000000000000 : ℝ) (504752855817/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0276; no trusted numerical premise.
theorem cover7_leaf0276_exp_radius : (997581414174610309/1000000000000000000 : ℝ) ≤ Real.exp ((-8887/458752 : ℝ)/8) ∧ Real.exp ((-8887/458752 : ℝ)/8) ≤ (99758141417461031/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8887/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0276_exp_lower : (114761141279048963/125000000000000000 : ℝ) ≤ Real.exp ((-5469491284373/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469491284373/8000000000000 : ℝ)/8) ≤ (183617826046478341/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469491284373/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0276_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901132913/100000000000 : ℝ) ≤ 4*Real.exp (4443/32768 : ℝ)*Real.exp (-mu (radius 7 (8887/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (201901132913/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8887/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0276_exp_radius
  have hrNumeric : (7846514489/8000000000 : ℝ) ≤ Real.exp (-8887/458752 : ℝ) ∧ Real.exp (-8887/458752 : ℝ) ≤ (490407155563/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7846514489/8000000000 : ℝ) ≤ (radius 7 (8887/65536 : ℝ)) ∧ (radius 7 (8887/65536 : ℝ)) ≤ (490407155563/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8887/65536 : ℝ)) (7846514489/8000000000 : ℝ) (490407155563/500000000000 : ℝ) (97472158961/500000000000 : ℝ) (24368039741/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8887/65536 : ℝ)) (7846514489/8000000000 : ℝ) (490407155563/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8887/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7846514489/8000000000 : ℝ) (490407155563/500000000000 : ℝ) (495203577781/500000000000 : ℝ) (990407155563/1000000000000 : ℝ) (495180348743/500000000000 : ℝ) (990360697487/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8887/65536 : ℝ)) 1 (495203577781/500000000000 : ℝ) (990407155563/1000000000000 : ℝ) (495180348743/500000000000 : ℝ) (990360697487/1000000000000 : ℝ) (247595981631/250000000000 : ℝ) (39615357061/40000000000 : ℝ) (990383926251/1000000000000 : ℝ) (990383926253/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8887/65536 : ℝ)) 2 (247595981631/250000000000 : ℝ) (39615357061/40000000000 : ℝ) (990383926251/1000000000000 : ℝ) (990383926253/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8887/65536 : ℝ)) 3 (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8887/65536 : ℝ)) 4 (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8887/65536 : ℝ)) 5 (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8887/65536 : ℝ)) 6 (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8887/65536 : ℝ)) 7 (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8887/65536 : ℝ))) (97472158961/500000000000 : ℝ) (24368039741/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8887/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97472158961/500000000000 : ℝ) (24368039741/125000000000 : ℝ) (597472158961/1000000000000 : ℝ) (149368039741/250000000000 : ℝ) (110381247819/250000000000 : ℝ) (110381247821/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8887/65536 : ℝ))) 1 (597472158961/1000000000000 : ℝ) (149368039741/250000000000 : ℝ) (110381247819/250000000000 : ℝ) (110381247821/250000000000 : ℝ) (259749287559/500000000000 : ℝ) (129874643781/250000000000 : ℝ) (16050423773/31250000000 : ℝ) (513613560743/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8887/65536 : ℝ))) 2 (259749287559/500000000000 : ℝ) (129874643781/250000000000 : ℝ) (16050423773/31250000000 : ℝ) (513613560743/1000000000000 : ℝ) (516556067927/1000000000000 : ℝ) (258278033967/500000000000 : ℝ) (516547687017/1000000000000 : ℝ) (20661907481/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8887/65536 : ℝ))) 3 (516556067927/1000000000000 : ℝ) (258278033967/500000000000 : ℝ) (516547687017/1000000000000 : ℝ) (20661907481/40000000000 : ℝ) (16142246171/31250000000 : ℝ) (12913796937/25000000000 : ℝ) (103310375491/200000000000 : ℝ) (516551877463/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8887/65536 : ℝ))) 4 (16142246171/31250000000 : ℝ) (12913796937/25000000000 : ℝ) (103310375491/200000000000 : ℝ) (516551877463/1000000000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8887/65536 : ℝ))) 5 (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8887/65536 : ℝ))) 6 (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8887/65536 : ℝ))) 7 (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8887/65536 : ℝ)) hmem 8 (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8887/65536 : ℝ))) hcmem 8 (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8887/65536 : ℝ)) (990383926387/1000000000000 : ℝ) (990383926389/1000000000000 : ℝ) (516551877463/1000000000000 : ℝ) (16142246171/31250000000 : ℝ) (819276010139/1000000000000 : ℝ) (204819002539/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0276_exp_lower
  have heNumeric : (201901132913/100000000000 : ℝ)/4 ≤ Real.exp (-5469491284373/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901132913/100000000000 : ℝ)/4 ≤ Real.exp ((4443/32768 : ℝ)-(204819002539/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4443/32768 : ℝ) (8887/65536 : ℝ) (204819002539/250000000000 : ℝ) (201901132913/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0277; no trusted numerical premise.
theorem cover7_leaf0277_exp_radius : (249395285588820891/250000000000000000 : ℝ) ≤ Real.exp ((-1111/57344 : ℝ)/8) ∧ Real.exp ((-1111/57344 : ℝ)/8) ≤ (199516228471056713/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1111/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0277_exp_lower : (36723565000559211/40000000000000000 : ℝ) ≤ Real.exp ((-10938983296297/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938983296297/16000000000000 : ℝ)/8) ≤ (229522281253495069/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938983296297/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0277_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505618661/500000000000 : ℝ) ≤ 4*Real.exp (8887/65536 : ℝ)*Real.exp (-mu (radius 7 (1111/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505618661/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1111/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0277_exp_radius
  have hrNumeric : (490406086561/500000000000 : ℝ) ≤ Real.exp (-1111/57344 : ℝ) ∧ Real.exp (-1111/57344 : ℝ) ≤ (980812173123/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490406086561/500000000000 : ℝ) ≤ (radius 7 (1111/8192 : ℝ)) ∧ (radius 7 (1111/8192 : ℝ)) ≤ (980812173123/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1111/8192 : ℝ)) (490406086561/500000000000 : ℝ) (980812173123/1000000000000 : ℝ) (194955074449/1000000000000 : ℝ) (38991014891/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1111/8192 : ℝ)) (490406086561/500000000000 : ℝ) (980812173123/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1111/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490406086561/500000000000 : ℝ) (980812173123/1000000000000 : ℝ) (990406086561/1000000000000 : ℝ) (495203043281/500000000000 : ℝ) (990359618079/1000000000000 : ℝ) (6189747613/6250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1111/8192 : ℝ)) 1 (990406086561/1000000000000 : ℝ) (495203043281/500000000000 : ℝ) (990359618079/1000000000000 : ℝ) (6189747613/6250000000 : ℝ) (6189892827/6250000000 : ℝ) (990382852321/1000000000000 : ℝ) (990382852047/1000000000000 : ℝ) (990382852049/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1111/8192 : ℝ)) 2 (6189892827/6250000000 : ℝ) (990382852321/1000000000000 : ℝ) (990382852047/1000000000000 : ℝ) (990382852049/1000000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1111/8192 : ℝ)) 3 (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1111/8192 : ℝ)) 4 (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1111/8192 : ℝ)) 5 (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1111/8192 : ℝ)) 6 (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1111/8192 : ℝ)) 7 (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1111/8192 : ℝ))) (194955074449/1000000000000 : ℝ) (38991014891/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1111/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194955074449/1000000000000 : ℝ) (38991014891/200000000000 : ℝ) (74684692153/125000000000 : ℝ) (149369384307/250000000000 : ℝ) (55192146527/125000000000 : ℝ) (1724754579/3906250000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1111/8192 : ℝ))) 1 (74684692153/125000000000 : ℝ) (149369384307/250000000000 : ℝ) (55192146527/125000000000 : ℝ) (1724754579/3906250000 : ℝ) (3246920967/6250000000 : ℝ) (259753677363/500000000000 : ℝ) (513622957283/1000000000000 : ℝ) (51362295729/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1111/8192 : ℝ))) 2 (3246920967/6250000000 : ℝ) (259753677363/500000000000 : ℝ) (513622957283/1000000000000 : ℝ) (51362295729/100000000000 : ℝ) (516565156001/1000000000000 : ℝ) (64570644501/125000000000 : ℝ) (516556776997/1000000000000 : ℝ) (129139194251/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1111/8192 : ℝ))) 3 (516565156001/1000000000000 : ℝ) (64570644501/125000000000 : ℝ) (516556776997/1000000000000 : ℝ) (129139194251/250000000000 : ℝ) (516560966499/1000000000000 : ℝ) (258280483253/500000000000 : ℝ) (258280483241/500000000000 : ℝ) (51656096649/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1111/8192 : ℝ))) 4 (516560966499/1000000000000 : ℝ) (258280483253/500000000000 : ℝ) (258280483241/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1111/8192 : ℝ))) 5 (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1111/8192 : ℝ))) 6 (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1111/8192 : ℝ))) 7 (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1111/8192 : ℝ)) hmem 8 (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1111/8192 : ℝ))) hcmem 8 (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1111/8192 : ℝ)) (990382852183/1000000000000 : ℝ) (198076570437/200000000000 : ℝ) (51656096649/100000000000 : ℝ) (258280483249/500000000000 : ℝ) (409645657201/500000000000 : ℝ) (819291314417/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0277_exp_lower
  have heNumeric : (1009505618661/500000000000 : ℝ)/4 ≤ Real.exp (-10938983296297/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505618661/500000000000 : ℝ)/4 ≤ Real.exp ((8887/65536 : ℝ)-(819291314417/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8887/65536 : ℝ) (1111/8192 : ℝ) (819291314417/1000000000000 : ℝ) (1009505618661/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0278; no trusted numerical premise.
theorem cover7_leaf0278_exp_radius : (997580870536030883/1000000000000000000 : ℝ) ≤ Real.exp ((-8889/458752 : ℝ)/8) ∧ Real.exp ((-8889/458752 : ℝ)/8) ≤ (249395217634007721/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8889/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0278_exp_lower : (918089119927544187/1000000000000000000 : ℝ) ≤ Real.exp ((-1367373000681/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367373000681/2000000000000 : ℝ)/8) ≤ (229522279981886047/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367373000681/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0278_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403802229567/200000000000 : ℝ) ≤ 4*Real.exp (1111/8192 : ℝ)*Real.exp (-mu (radius 7 (8889/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (403802229567/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8889/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0278_exp_radius
  have hrNumeric : (245202508781/250000000000 : ℝ) ≤ Real.exp (-8889/458752 : ℝ) ∧ Real.exp (-8889/458752 : ℝ) ≤ (7846480281/8000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245202508781/250000000000 : ℝ) ≤ (radius 7 (8889/65536 : ℝ)) ∧ (radius 7 (8889/65536 : ℝ)) ≤ (7846480281/8000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8889/65536 : ℝ)) (245202508781/250000000000 : ℝ) (7846480281/8000000000 : ℝ) (97482915167/500000000000 : ℝ) (9748291517/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8889/65536 : ℝ)) (245202508781/250000000000 : ℝ) (7846480281/8000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8889/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245202508781/250000000000 : ℝ) (7846480281/8000000000 : ℝ) (495202508781/500000000000 : ℝ) (990405017563/1000000000000 : ℝ) (990358538673/1000000000000 : ℝ) (39614341547/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8889/65536 : ℝ)) 1 (495202508781/500000000000 : ℝ) (990405017563/1000000000000 : ℝ) (990358538673/1000000000000 : ℝ) (39614341547/40000000000 : ℝ) (990381778117/1000000000000 : ℝ) (990381778119/1000000000000 : ℝ) (247595444461/250000000000 : ℝ) (990381777847/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8889/65536 : ℝ)) 2 (990381778117/1000000000000 : ℝ) (990381778119/1000000000000 : ℝ) (247595444461/250000000000 : ℝ) (990381777847/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8889/65536 : ℝ)) 3 (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8889/65536 : ℝ)) 4 (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8889/65536 : ℝ)) 5 (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8889/65536 : ℝ)) 6 (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8889/65536 : ℝ)) 7 (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8889/65536 : ℝ))) (97482915167/500000000000 : ℝ) (9748291517/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8889/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97482915167/500000000000 : ℝ) (9748291517/50000000000 : ℝ) (597482915167/1000000000000 : ℝ) (59748291517/100000000000 : ℝ) (441549352093/1000000000000 : ℝ) (441549352101/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8889/65536 : ℝ))) 1 (597482915167/1000000000000 : ℝ) (59748291517/100000000000 : ℝ) (441549352093/1000000000000 : ℝ) (441549352101/1000000000000 : ℝ) (51951613363/100000000000 : ℝ) (129879033409/250000000000 : ℝ) (513632353029/1000000000000 : ℝ) (128408088259/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8889/65536 : ℝ))) 2 (51951613363/100000000000 : ℝ) (129879033409/250000000000 : ℝ) (513632353029/1000000000000 : ℝ) (128408088259/250000000000 : ℝ) (516574243329/1000000000000 : ℝ) (64571780417/125000000000 : ℝ) (129141466557/250000000000 : ℝ) (129141466559/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8889/65536 : ℝ))) 3 (516574243329/1000000000000 : ℝ) (64571780417/125000000000 : ℝ) (129141466557/250000000000 : ℝ) (129141466559/250000000000 : ℝ) (258285027389/500000000000 : ℝ) (258285027393/500000000000 : ℝ) (516570054761/1000000000000 : ℝ) (51657005477/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8889/65536 : ℝ))) 4 (258285027389/500000000000 : ℝ) (258285027393/500000000000 : ℝ) (516570054761/1000000000000 : ℝ) (51657005477/100000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8889/65536 : ℝ))) 5 (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8889/65536 : ℝ))) 6 (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8889/65536 : ℝ))) 7 (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8889/65536 : ℝ)) hmem 8 (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8889/65536 : ℝ))) hcmem 8 (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8889/65536 : ℝ)) (49519088899/50000000000 : ℝ) (990381777983/1000000000000 : ℝ) (516570054769/1000000000000 : ℝ) (258285027389/500000000000 : ℝ) (81930661751/100000000000 : ℝ) (102413327191/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0278_exp_lower
  have heNumeric : (403802229567/200000000000 : ℝ)/4 ≤ Real.exp (-1367373000681/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403802229567/200000000000 : ℝ)/4 ≤ Real.exp ((1111/8192 : ℝ)-(102413327191/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1111/8192 : ℝ) (8889/65536 : ℝ) (102413327191/125000000000 : ℝ) (403802229567/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0279; no trusted numerical premise.
theorem cover7_leaf0279_exp_radius : (249395149679213067/250000000000000000 : ℝ) ≤ Real.exp ((-635/32768 : ℝ)/8) ∧ Real.exp ((-635/32768 : ℝ)/8) ≤ (997580598716852269/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-635/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0279_exp_lower : (183617822994570783/200000000000000000 : ℝ) ≤ Real.exp ((-10938984696231/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938984696231/16000000000000 : ℝ)/8) ≤ (229522278743213479/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938984696231/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0279_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019011060667/1000000000000 : ℝ) ≤ 4*Real.exp (8889/65536 : ℝ)*Real.exp (-mu (radius 7 (4445/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (2019011060667/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4445/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0279_exp_radius
  have hrNumeric : (98080789713/100000000000 : ℝ) ≤ Real.exp (-635/32768 : ℝ) ∧ Real.exp (-635/32768 : ℝ) ≤ (980807897131/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98080789713/100000000000 : ℝ) ≤ (radius 7 (4445/32768 : ℝ)) ∧ (radius 7 (4445/32768 : ℝ)) ≤ (980807897131/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4445/32768 : ℝ)) (98080789713/100000000000 : ℝ) (980807897131/1000000000000 : ℝ) (97488292791/500000000000 : ℝ) (48744146397/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4445/32768 : ℝ)) (98080789713/100000000000 : ℝ) (980807897131/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4445/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98080789713/100000000000 : ℝ) (980807897131/1000000000000 : ℝ) (198080789713/200000000000 : ℝ) (495201974283/500000000000 : ℝ) (990357459269/1000000000000 : ℝ) (99035745927/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4445/32768 : ℝ)) 1 (198080789713/200000000000 : ℝ) (495201974283/500000000000 : ℝ) (990357459269/1000000000000 : ℝ) (99035745927/100000000000 : ℝ) (990380703917/1000000000000 : ℝ) (495190351959/500000000000 : ℝ) (247595175911/250000000000 : ℝ) (495190351823/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4445/32768 : ℝ)) 2 (990380703917/1000000000000 : ℝ) (495190351959/500000000000 : ℝ) (247595175911/250000000000 : ℝ) (495190351823/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4445/32768 : ℝ)) 3 (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4445/32768 : ℝ)) 4 (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4445/32768 : ℝ)) 5 (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4445/32768 : ℝ)) 6 (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4445/32768 : ℝ)) 7 (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4445/32768 : ℝ))) (97488292791/500000000000 : ℝ) (48744146397/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4445/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97488292791/500000000000 : ℝ) (48744146397/250000000000 : ℝ) (597488292791/1000000000000 : ℝ) (298744146397/500000000000 : ℝ) (13798797841/31250000000 : ℝ) (11039038273/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4445/32768 : ℝ))) 1 (597488292791/1000000000000 : ℝ) (298744146397/500000000000 : ℝ) (13798797841/31250000000 : ℝ) (11039038273/25000000000 : ℝ) (519524911851/1000000000000 : ℝ) (519524911857/1000000000000 : ℝ) (256820873989/500000000000 : ℝ) (102728349597/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4445/32768 : ℝ))) 2 (519524911851/1000000000000 : ℝ) (519524911857/1000000000000 : ℝ) (256820873989/500000000000 : ℝ) (102728349597/200000000000 : ℝ) (258291664957/500000000000 : ℝ) (516583329921/1000000000000 : ℝ) (516574954717/1000000000000 : ℝ) (129143738681/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4445/32768 : ℝ))) 3 (258291664957/500000000000 : ℝ) (516583329921/1000000000000 : ℝ) (516574954717/1000000000000 : ℝ) (129143738681/250000000000 : ℝ) (103315828463/200000000000 : ℝ) (516579142323/1000000000000 : ℝ) (258289571149/500000000000 : ℝ) (258289571153/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4445/32768 : ℝ))) 4 (103315828463/200000000000 : ℝ) (516579142323/1000000000000 : ℝ) (258289571149/500000000000 : ℝ) (258289571153/500000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4445/32768 : ℝ))) 5 (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4445/32768 : ℝ))) 6 (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4445/32768 : ℝ))) 7 (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4445/32768 : ℝ)) hmem 8 (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4445/32768 : ℝ))) hcmem 8 (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4445/32768 : ℝ)) (49519035189/50000000000 : ℝ) (495190351891/500000000000 : ℝ) (258289571153/500000000000 : ℝ) (103315828463/200000000000 : ℝ) (409660959737/500000000000 : ℝ) (819321919491/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0279_exp_lower
  have heNumeric : (2019011060667/1000000000000 : ℝ)/4 ≤ Real.exp (-10938984696231/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019011060667/1000000000000 : ℝ)/4 ≤ Real.exp ((8889/65536 : ℝ)-(819321919491/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8889/65536 : ℝ) (4445/32768 : ℝ) (819321919491/1000000000000 : ℝ) (2019011060667/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0280; no trusted numerical premise.
theorem cover7_leaf0280_exp_radius : (997580326897747717/1000000000000000000 : ℝ) ≤ Real.exp ((-8891/458752 : ℝ)/8) ∧ Real.exp ((-8891/458752 : ℝ)/8) ≤ (498790163448873859/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8891/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0280_exp_lower : (918089110149450413/1000000000000000000 : ℝ) ≤ Real.exp ((-1093898536871/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093898536871/1600000000000 : ℝ)/8) ≤ (459044555074725207/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093898536871/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0280_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (31547046497/15625000000 : ℝ) ≤ 4*Real.exp (4445/32768 : ℝ)*Real.exp (-mu (radius 7 (8891/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (31547046497/15625000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8891/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0280_exp_radius
  have hrNumeric : (49040287957/50000000000 : ℝ) ≤ Real.exp (-8891/458752 : ℝ) ∧ Real.exp (-8891/458752 : ℝ) ≤ (980805759141/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49040287957/50000000000 : ℝ) ≤ (radius 7 (8891/65536 : ℝ)) ∧ (radius 7 (8891/65536 : ℝ)) ≤ (980805759141/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8891/65536 : ℝ)) (49040287957/50000000000 : ℝ) (980805759141/1000000000000 : ℝ) (194987340193/1000000000000 : ℝ) (194987340199/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8891/65536 : ℝ)) (49040287957/50000000000 : ℝ) (980805759141/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8891/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49040287957/50000000000 : ℝ) (980805759141/1000000000000 : ℝ) (99040287957/100000000000 : ℝ) (990402879571/1000000000000 : ℝ) (198071275973/200000000000 : ℝ) (495178189933/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8891/65536 : ℝ)) 1 (99040287957/100000000000 : ℝ) (990402879571/1000000000000 : ℝ) (198071275973/200000000000 : ℝ) (495178189933/500000000000 : ℝ) (990379629717/1000000000000 : ℝ) (990379629719/1000000000000 : ℝ) (247594907361/250000000000 : ℝ) (495189814723/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8891/65536 : ℝ)) 2 (990379629717/1000000000000 : ℝ) (990379629719/1000000000000 : ℝ) (247594907361/250000000000 : ℝ) (495189814723/500000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8891/65536 : ℝ)) 3 (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8891/65536 : ℝ)) 4 (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8891/65536 : ℝ)) 5 (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8891/65536 : ℝ)) 6 (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8891/65536 : ℝ)) 7 (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8891/65536 : ℝ))) (194987340193/1000000000000 : ℝ) (194987340199/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8891/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (194987340193/1000000000000 : ℝ) (194987340199/1000000000000 : ℝ) (37343354381/62500000000 : ℝ) (5974936701/10000000000 : ℝ) (17662948347/40000000000 : ℝ) (220786854341/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8891/65536 : ℝ))) 1 (37343354381/62500000000 : ℝ) (5974936701/10000000000 : ℝ) (17662948347/40000000000 : ℝ) (220786854341/500000000000 : ℝ) (103906737877/200000000000 : ℝ) (519533689391/1000000000000 : ℝ) (128412785533/250000000000 : ℝ) (513651142139/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8891/65536 : ℝ))) 2 (103906737877/200000000000 : ℝ) (519533689391/1000000000000 : ℝ) (128412785533/250000000000 : ℝ) (513651142139/1000000000000 : ℝ) (258296207879/500000000000 : ℝ) (103318483153/200000000000 : ℝ) (16143251327/31250000000 : ℝ) (516584042471/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8891/65536 : ℝ))) 3 (258296207879/500000000000 : ℝ) (103318483153/200000000000 : ℝ) (16143251327/31250000000 : ℝ) (516584042471/1000000000000 : ℝ) (516588229111/1000000000000 : ℝ) (258294114559/500000000000 : ℝ) (258294114547/500000000000 : ℝ) (258294114551/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8891/65536 : ℝ))) 4 (516588229111/1000000000000 : ℝ) (258294114559/500000000000 : ℝ) (258294114547/500000000000 : ℝ) (258294114551/500000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8891/65536 : ℝ))) 5 (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8891/65536 : ℝ))) 6 (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8891/65536 : ℝ))) 7 (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8891/65536 : ℝ)) hmem 8 (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8891/65536 : ℝ))) hcmem 8 (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8891/65536 : ℝ)) (49518981479/50000000000 : ℝ) (990379629583/1000000000000 : ℝ) (258294114551/500000000000 : ℝ) (51658822911/100000000000 : ℝ) (409668610147/500000000000 : ℝ) (81933722031/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0280_exp_lower
  have heNumeric : (31547046497/15625000000 : ℝ)/4 ≤ Real.exp (-1093898536871/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (31547046497/15625000000 : ℝ)/4 ≤ Real.exp ((4445/32768 : ℝ)-(81933722031/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4445/32768 : ℝ) (8891/65536 : ℝ) (81933722031/100000000000 : ℝ) (31547046497/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0281; no trusted numerical premise.
theorem cover7_leaf0281_exp_radius : (997580055078717231/1000000000000000000 : ℝ) ≤ Real.exp ((-2223/114688 : ℝ)/8) ∧ Real.exp ((-2223/114688 : ℝ)/8) ≤ (62348753442419827/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2223/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0281_exp_lower : (918089105458940333/1000000000000000000 : ℝ) ≤ Real.exp ((-10938986022661/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938986022661/16000000000000 : ℝ)/8) ≤ (459044552729470167/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938986022661/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0281_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010893287/1000000000000 : ℝ) ≤ 4*Real.exp (8891/65536 : ℝ)*Real.exp (-mu (radius 7 (2223/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010893287/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2223/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0281_exp_radius
  have hrNumeric : (245200905289/250000000000 : ℝ) ≤ Real.exp (-2223/114688 : ℝ) ∧ Real.exp (-2223/114688 : ℝ) ≤ (980803621157/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245200905289/250000000000 : ℝ) ≤ (radius 7 (2223/16384 : ℝ)) ∧ (radius 7 (2223/16384 : ℝ)) ≤ (980803621157/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2223/16384 : ℝ)) (245200905289/250000000000 : ℝ) (980803621157/1000000000000 : ℝ) (97499047079/500000000000 : ℝ) (48749523541/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2223/16384 : ℝ)) (245200905289/250000000000 : ℝ) (980803621157/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2223/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245200905289/250000000000 : ℝ) (980803621157/1000000000000 : ℝ) (495200905289/500000000000 : ℝ) (990401810579/1000000000000 : ℝ) (990355300463/1000000000000 : ℝ) (61897206279/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2223/16384 : ℝ)) 1 (495200905289/500000000000 : ℝ) (990401810579/1000000000000 : ℝ) (990355300463/1000000000000 : ℝ) (61897206279/62500000000 : ℝ) (1547466493/1562500000 : ℝ) (495189277761/500000000000 : ℝ) (990378555247/1000000000000 : ℝ) (990378555249/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2223/16384 : ℝ)) 2 (1547466493/1562500000 : ℝ) (495189277761/500000000000 : ℝ) (990378555247/1000000000000 : ℝ) (990378555249/1000000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2223/16384 : ℝ)) 3 (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2223/16384 : ℝ)) 4 (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2223/16384 : ℝ)) 5 (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2223/16384 : ℝ)) 6 (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2223/16384 : ℝ)) 7 (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2223/16384 : ℝ))) (97499047079/500000000000 : ℝ) (48749523541/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2223/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97499047079/500000000000 : ℝ) (48749523541/250000000000 : ℝ) (597499047079/1000000000000 : ℝ) (298749523541/500000000000 : ℝ) (441585885369/1000000000000 : ℝ) (441585885377/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2223/16384 : ℝ))) 1 (597499047079/1000000000000 : ℝ) (298749523541/500000000000 : ℝ) (441585885369/1000000000000 : ℝ) (441585885377/1000000000000 : ℝ) (32471404139/62500000000 : ℝ) (51954246623/100000000000 : ℝ) (513660535481/1000000000000 : ℝ) (8025945867/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2223/16384 : ℝ))) 2 (32471404139/62500000000 : ℝ) (51954246623/100000000000 : ℝ) (513660535481/1000000000000 : ℝ) (8025945867/15625000000 : ℝ) (129150375213/250000000000 : ℝ) (516601500859/1000000000000 : ℝ) (25829656473/50000000000 : ℝ) (516593129467/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2223/16384 : ℝ))) 3 (129150375213/250000000000 : ℝ) (516601500859/1000000000000 : ℝ) (25829656473/50000000000 : ℝ) (516593129467/1000000000000 : ℝ) (129149328789/250000000000 : ℝ) (516597315163/1000000000000 : ℝ) (516597315139/1000000000000 : ℝ) (516597315147/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2223/16384 : ℝ))) 4 (129149328789/250000000000 : ℝ) (516597315163/1000000000000 : ℝ) (516597315139/1000000000000 : ℝ) (516597315147/1000000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2223/16384 : ℝ))) 5 (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2223/16384 : ℝ))) 6 (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2223/16384 : ℝ))) 7 (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2223/16384 : ℝ)) hmem 8 (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2223/16384 : ℝ))) hcmem 8 (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2223/16384 : ℝ)) (990378555383/1000000000000 : ℝ) (495189277693/500000000000 : ℝ) (516597315147/1000000000000 : ℝ) (103319463031/200000000000 : ℝ) (163870503991/200000000000 : ℝ) (819352519971/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0281_exp_lower
  have heNumeric : (2019010893287/1000000000000 : ℝ)/4 ≤ Real.exp (-10938986022661/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010893287/1000000000000 : ℝ)/4 ≤ Real.exp ((8891/65536 : ℝ)-(819352519971/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8891/65536 : ℝ) (2223/16384 : ℝ) (819352519971/1000000000000 : ℝ) (2019010893287/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0282; no trusted numerical premise.
theorem cover7_leaf0282_exp_radius : (99757978325976081/100000000000000000 : ℝ) ≤ Real.exp ((-8893/458752 : ℝ)/8) ∧ Real.exp ((-8893/458752 : ℝ)/8) ≤ (997579783259760811/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8893/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0282_exp_lower : (918089100899831781/1000000000000000000 : ℝ) ≤ Real.exp ((-2734746664573/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734746664573/4000000000000 : ℝ)/8) ≤ (459044550449915891/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734746664573/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0282_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505406539/500000000000 : ℝ) ≤ 4*Real.exp (2223/16384 : ℝ)*Real.exp (-mu (radius 7 (8893/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505406539/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8893/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0282_exp_radius
  have hrNumeric : (122600185397/125000000000 : ℝ) ≤ Real.exp (-8893/458752 : ℝ) ∧ Real.exp (-8893/458752 : ℝ) ≤ (980801483177/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122600185397/125000000000 : ℝ) ≤ (radius 7 (8893/65536 : ℝ)) ∧ (radius 7 (8893/65536 : ℝ)) ≤ (980801483177/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8893/65536 : ℝ)) (122600185397/125000000000 : ℝ) (980801483177/1000000000000 : ℝ) (39001769497/200000000000 : ℝ) (195008847491/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8893/65536 : ℝ)) (122600185397/125000000000 : ℝ) (980801483177/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8893/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122600185397/125000000000 : ℝ) (980801483177/1000000000000 : ℝ) (247600185397/250000000000 : ℝ) (990400741589/1000000000000 : ℝ) (495177110531/500000000000 : ℝ) (990354221063/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8893/65536 : ℝ)) 1 (247600185397/250000000000 : ℝ) (990400741589/1000000000000 : ℝ) (495177110531/500000000000 : ℝ) (990354221063/1000000000000 : ℝ) (39615099253/40000000000 : ℝ) (495188740663/500000000000 : ℝ) (990377481051/1000000000000 : ℝ) (990377481053/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8893/65536 : ℝ)) 2 (39615099253/40000000000 : ℝ) (495188740663/500000000000 : ℝ) (990377481051/1000000000000 : ℝ) (990377481053/1000000000000 : ℝ) (247594370297/250000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8893/65536 : ℝ)) 3 (247594370297/250000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8893/65536 : ℝ)) 4 (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8893/65536 : ℝ)) 5 (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8893/65536 : ℝ)) 6 (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8893/65536 : ℝ)) 7 (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8893/65536 : ℝ))) (39001769497/200000000000 : ℝ) (195008847491/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8893/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (39001769497/200000000000 : ℝ) (195008847491/1000000000000 : ℝ) (298752211871/500000000000 : ℝ) (298752211873/500000000000 : ℝ) (220799030503/500000000000 : ℝ) (220799030507/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8893/65536 : ℝ))) 1 (298752211871/500000000000 : ℝ) (298752211873/500000000000 : ℝ) (220799030503/500000000000 : ℝ) (220799030507/500000000000 : ℝ) (259775621187/500000000000 : ℝ) (25977562119/50000000000 : ℝ) (256834964017/500000000000 : ℝ) (513669928041/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8893/65536 : ℝ))) 2 (259775621187/500000000000 : ℝ) (25977562119/50000000000 : ℝ) (256834964017/500000000000 : ℝ) (513669928041/1000000000000 : ℝ) (129152646301/250000000000 : ℝ) (516610585211/1000000000000 : ℝ) (516602215713/1000000000000 : ℝ) (516602215721/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8893/65536 : ℝ))) 3 (129152646301/250000000000 : ℝ) (516610585211/1000000000000 : ℝ) (516602215713/1000000000000 : ℝ) (516602215721/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (258303200233/500000000000 : ℝ) (516606400441/1000000000000 : ℝ) (10332128009/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8893/65536 : ℝ))) 4 (258303200229/500000000000 : ℝ) (258303200233/500000000000 : ℝ) (516606400441/1000000000000 : ℝ) (10332128009/20000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8893/65536 : ℝ))) 5 (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8893/65536 : ℝ))) 6 (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8893/65536 : ℝ))) 7 (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8893/65536 : ℝ)) hmem 8 (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8893/65536 : ℝ))) hcmem 8 (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8893/65536 : ℝ)) (990377481187/1000000000000 : ℝ) (99037748119/100000000000 : ℝ) (516606400449/1000000000000 : ℝ) (258303200229/500000000000 : ℝ) (819367818469/1000000000000 : ℝ) (819367818487/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0282_exp_lower
  have heNumeric : (1009505406539/500000000000 : ℝ)/4 ≤ Real.exp (-2734746664573/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505406539/500000000000 : ℝ)/4 ≤ Real.exp ((2223/16384 : ℝ)-(819367818487/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2223/16384 : ℝ) (8893/65536 : ℝ) (819367818487/1000000000000 : ℝ) (1009505406539/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0283; no trusted numerical premise.
theorem cover7_leaf0283_exp_radius : (997579511440878453/1000000000000000000 : ℝ) ≤ Real.exp ((-4447/229376 : ℝ)/8) ∧ Real.exp ((-4447/229376 : ℝ)/8) ≤ (498789755720439227/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4447/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0283_exp_lower : (459044548236349279/500000000000000000 : ℝ) ≤ Real.exp ((-10938987275523/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938987275523/16000000000000 : ℝ)/8) ≤ (918089096472698559/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938987275523/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0283_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901073519/100000000000 : ℝ) ≤ 4*Real.exp (8893/65536 : ℝ)*Real.exp (-mu (radius 7 (4447/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (201901073519/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4447/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0283_exp_radius
  have hrNumeric : (980799345201/1000000000000 : ℝ) ≤ Real.exp (-4447/229376 : ℝ) ∧ Real.exp (-4447/229376 : ℝ) ≤ (490399672601/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980799345201/1000000000000 : ℝ) ≤ (radius 7 (4447/32768 : ℝ)) ∧ (radius 7 (4447/32768 : ℝ)) ≤ (490399672601/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4447/32768 : ℝ)) (980799345201/1000000000000 : ℝ) (490399672601/500000000000 : ℝ) (48754900043/250000000000 : ℝ) (97509800089/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4447/32768 : ℝ)) (980799345201/1000000000000 : ℝ) (490399672601/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4447/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980799345201/1000000000000 : ℝ) (490399672601/500000000000 : ℝ) (4951998363/5000000000 : ℝ) (990399672601/1000000000000 : ℝ) (495176570831/500000000000 : ℝ) (30948535677/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4447/32768 : ℝ)) 1 (4951998363/5000000000 : ℝ) (990399672601/1000000000000 : ℝ) (495176570831/500000000000 : ℝ) (30948535677/31250000000 : ℝ) (990376407131/1000000000000 : ℝ) (990376407133/1000000000000 : ℝ) (990376406857/1000000000000 : ℝ) (49518820343/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4447/32768 : ℝ)) 2 (990376407131/1000000000000 : ℝ) (990376407133/1000000000000 : ℝ) (990376406857/1000000000000 : ℝ) (49518820343/50000000000 : ℝ) (495188203497/500000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4447/32768 : ℝ)) 3 (495188203497/500000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4447/32768 : ℝ)) 4 (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4447/32768 : ℝ)) 5 (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4447/32768 : ℝ)) 6 (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4447/32768 : ℝ)) 7 (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4447/32768 : ℝ))) (48754900043/250000000000 : ℝ) (97509800089/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4447/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48754900043/250000000000 : ℝ) (97509800089/500000000000 : ℝ) (298754900043/500000000000 : ℝ) (597509800089/1000000000000 : ℝ) (441610235583/1000000000000 : ℝ) (441610235591/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4447/32768 : ℝ))) 1 (298754900043/500000000000 : ℝ) (597509800089/1000000000000 : ℝ) (441610235583/1000000000000 : ℝ) (441610235591/1000000000000 : ℝ) (259780008917/500000000000 : ℝ) (6494500223/12500000000 : ℝ) (513679319789/1000000000000 : ℝ) (128419829949/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4447/32768 : ℝ))) 2 (259780008917/500000000000 : ℝ) (6494500223/12500000000 : ℝ) (513679319789/1000000000000 : ℝ) (128419829949/250000000000 : ℝ) (516619668811/1000000000000 : ℝ) (258309834409/500000000000 : ℝ) (258305650611/500000000000 : ℝ) (516611301229/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4447/32768 : ℝ))) 3 (516619668811/1000000000000 : ℝ) (258309834409/500000000000 : ℝ) (258305650611/500000000000 : ℝ) (516611301229/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (16144233907/31250000000 : ℝ) (516615484999/1000000000000 : ℝ) (516615485007/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4447/32768 : ℝ))) 4 (64576935627/125000000000 : ℝ) (16144233907/31250000000 : ℝ) (516615484999/1000000000000 : ℝ) (516615485007/1000000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4447/32768 : ℝ))) 5 (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4447/32768 : ℝ))) 6 (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4447/32768 : ℝ))) 7 (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4447/32768 : ℝ)) hmem 8 (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4447/32768 : ℝ))) hcmem 8 (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4447/32768 : ℝ)) (990376406993/1000000000000 : ℝ) (990376406997/1000000000000 : ℝ) (516615485007/1000000000000 : ℝ) (64576935627/125000000000 : ℝ) (409691557917/500000000000 : ℝ) (819383115853/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0283_exp_lower
  have heNumeric : (201901073519/100000000000 : ℝ)/4 ≤ Real.exp (-10938987275523/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901073519/100000000000 : ℝ)/4 ≤ Real.exp ((8893/65536 : ℝ)-(819383115853/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8893/65536 : ℝ) (4447/32768 : ℝ) (819383115853/1000000000000 : ℝ) (201901073519/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0284; no trusted numerical premise.
theorem cover7_leaf0284_exp_radius : (997579239622070161/1000000000000000000 : ℝ) ≤ Real.exp ((-8895/458752 : ℝ)/8) ∧ Real.exp ((-8895/458752 : ℝ)/8) ≤ (498789619811035081/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8895/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0284_exp_lower : (918089092177196381/1000000000000000000 : ℝ) ≤ Real.exp ((-5469493937201/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469493937201/8000000000000 : ℝ)/8) ≤ (459044546088598191/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469493937201/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0284_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010659619/1000000000000 : ℝ) ≤ 4*Real.exp (4447/32768 : ℝ)*Real.exp (-mu (radius 7 (8895/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010659619/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8895/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0284_exp_radius
  have hrNumeric : (98079720723/100000000000 : ℝ) ≤ Real.exp (-8895/458752 : ℝ) ∧ Real.exp (-8895/458752 : ℝ) ≤ (980797207231/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98079720723/100000000000 : ℝ) ≤ (radius 7 (8895/65536 : ℝ)) ∧ (radius 7 (8895/65536 : ℝ)) ≤ (980797207231/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8895/65536 : ℝ)) (98079720723/100000000000 : ℝ) (980797207231/1000000000000 : ℝ) (97515176111/500000000000 : ℝ) (48757588057/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8895/65536 : ℝ)) (98079720723/100000000000 : ℝ) (980797207231/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8895/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98079720723/100000000000 : ℝ) (980797207231/1000000000000 : ℝ) (198079720723/200000000000 : ℝ) (30949956363/31250000000 : ℝ) (990352062263/1000000000000 : ℝ) (198070412453/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8895/65536 : ℝ)) 1 (198079720723/200000000000 : ℝ) (30949956363/31250000000 : ℝ) (990352062263/1000000000000 : ℝ) (198070412453/200000000000 : ℝ) (990375332939/1000000000000 : ℝ) (990375332941/1000000000000 : ℝ) (198075066533/200000000000 : ℝ) (247593833167/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8895/65536 : ℝ)) 2 (990375332939/1000000000000 : ℝ) (990375332941/1000000000000 : ℝ) (198075066533/200000000000 : ℝ) (247593833167/250000000000 : ℝ) (495187666401/500000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8895/65536 : ℝ)) 3 (495187666401/500000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8895/65536 : ℝ)) 4 (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8895/65536 : ℝ)) 5 (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8895/65536 : ℝ)) 6 (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8895/65536 : ℝ)) 7 (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8895/65536 : ℝ))) (97515176111/500000000000 : ℝ) (48757588057/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8895/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97515176111/500000000000 : ℝ) (48757588057/250000000000 : ℝ) (597515176111/1000000000000 : ℝ) (298757588057/500000000000 : ℝ) (441622409103/1000000000000 : ℝ) (44162240911/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8895/65536 : ℝ))) 1 (597515176111/1000000000000 : ℝ) (298757588057/500000000000 : ℝ) (441622409103/1000000000000 : ℝ) (44162240911/100000000000 : ℝ) (519568792607/1000000000000 : ℝ) (129892198153/250000000000 : ℝ) (513688710747/1000000000000 : ℝ) (256844355377/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8895/65536 : ℝ))) 2 (519568792607/1000000000000 : ℝ) (129892198153/250000000000 : ℝ) (513688710747/1000000000000 : ℝ) (256844355377/500000000000 : ℝ) (516628751677/1000000000000 : ℝ) (516628751683/1000000000000 : ℝ) (129155096497/250000000000 : ℝ) (103324077199/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8895/65536 : ℝ))) 3 (516628751677/1000000000000 : ℝ) (516628751683/1000000000000 : ℝ) (129155096497/250000000000 : ℝ) (103324077199/200000000000 : ℝ) (1009032361/1953125000 : ℝ) (516624568839/1000000000000 : ℝ) (103324913763/200000000000 : ℝ) (516624568823/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8895/65536 : ℝ))) 4 (1009032361/1953125000 : ℝ) (516624568839/1000000000000 : ℝ) (103324913763/200000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8895/65536 : ℝ))) 5 (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8895/65536 : ℝ))) 6 (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8895/65536 : ℝ))) 7 (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8895/65536 : ℝ)) hmem 8 (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8895/65536 : ℝ))) hcmem 8 (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8895/65536 : ℝ)) (990375332801/1000000000000 : ℝ) (198075066561/200000000000 : ℝ) (516624568823/1000000000000 : ℝ) (516624568831/1000000000000 : ℝ) (163879682411/200000000000 : ℝ) (102424801509/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0284_exp_lower
  have heNumeric : (2019010659619/1000000000000 : ℝ)/4 ≤ Real.exp (-5469493937201/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010659619/1000000000000 : ℝ)/4 ≤ Real.exp ((4447/32768 : ℝ)-(102424801509/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4447/32768 : ℝ) (8895/65536 : ℝ) (102424801509/125000000000 : ℝ) (2019010659619/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0285; no trusted numerical premise.
theorem cover7_leaf0285_exp_radius : (498789483901667967/500000000000000000 : ℝ) ≤ Real.exp ((-139/7168 : ℝ)/8) ∧ Real.exp ((-139/7168 : ℝ)/8) ≤ (199515793560667187/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-139/7168 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0285_exp_lower : (91808908801366953/100000000000000000 : ℝ) ≤ Real.exp ((-10938988454881/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938988454881/16000000000000 : ℝ)/8) ≤ (918089088013669531/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938988454881/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0285_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010586369/1000000000000 : ℝ) ≤ 4*Real.exp (8895/65536 : ℝ)*Real.exp (-mu (radius 7 (139/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010586369/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (139/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0285_exp_radius
  have hrNumeric : (61299691829/62500000000 : ℝ) ≤ Real.exp (-139/7168 : ℝ) ∧ Real.exp (-139/7168 : ℝ) ≤ (196159013853/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61299691829/62500000000 : ℝ) ≤ (radius 7 (139/1024 : ℝ)) ∧ (radius 7 (139/1024 : ℝ)) ≤ (196159013853/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (139/1024 : ℝ)) (61299691829/62500000000 : ℝ) (196159013853/200000000000 : ℝ) (19504110363/100000000000 : ℝ) (48760275909/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (139/1024 : ℝ)) (61299691829/62500000000 : ℝ) (196159013853/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (139/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61299691829/62500000000 : ℝ) (196159013853/200000000000 : ℝ) (123799691829/125000000000 : ℝ) (990397534633/1000000000000 : ℝ) (495175491433/500000000000 : ℝ) (990350982867/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (139/1024 : ℝ)) 1 (123799691829/125000000000 : ℝ) (990397534633/1000000000000 : ℝ) (495175491433/500000000000 : ℝ) (990350982867/1000000000000 : ℝ) (990374258749/1000000000000 : ℝ) (792299407/800000000 : ℝ) (39614970339/40000000000 : ℝ) (990374258477/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (139/1024 : ℝ)) 2 (990374258749/1000000000000 : ℝ) (792299407/800000000 : ℝ) (39614970339/40000000000 : ℝ) (990374258477/1000000000000 : ℝ) (247593564653/250000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (139/1024 : ℝ)) 3 (247593564653/250000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (139/1024 : ℝ)) 4 (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (139/1024 : ℝ)) 5 (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (139/1024 : ℝ)) 6 (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (139/1024 : ℝ)) 7 (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (139/1024 : ℝ))) (19504110363/100000000000 : ℝ) (48760275909/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (139/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19504110363/100000000000 : ℝ) (48760275909/250000000000 : ℝ) (119504110363/200000000000 : ℝ) (298760275909/500000000000 : ℝ) (11040864539/25000000000 : ℝ) (6900540337/15625000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (139/1024 : ℝ))) 1 (119504110363/200000000000 : ℝ) (298760275909/500000000000 : ℝ) (11040864539/25000000000 : ℝ) (6900540337/15625000000 : ℝ) (519577566687/1000000000000 : ℝ) (519577566693/1000000000000 : ℝ) (102739620181/200000000000 : ℝ) (32106131307/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (139/1024 : ℝ))) 2 (519577566687/1000000000000 : ℝ) (519577566693/1000000000000 : ℝ) (102739620181/200000000000 : ℝ) (32106131307/62500000000 : ℝ) (129159458449/250000000000 : ℝ) (516637833803/1000000000000 : ℝ) (516629470007/1000000000000 : ℝ) (258314735007/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (139/1024 : ℝ))) 3 (129159458449/250000000000 : ℝ) (516637833803/1000000000000 : ℝ) (516629470007/1000000000000 : ℝ) (258314735007/500000000000 : ℝ) (516633651901/1000000000000 : ℝ) (516633651909/1000000000000 : ℝ) (129158412971/250000000000 : ℝ) (129158412973/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (139/1024 : ℝ))) 4 (516633651901/1000000000000 : ℝ) (516633651909/1000000000000 : ℝ) (129158412971/250000000000 : ℝ) (129158412973/250000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (139/1024 : ℝ))) 5 (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (139/1024 : ℝ))) 6 (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (139/1024 : ℝ))) 7 (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (139/1024 : ℝ)) hmem 8 (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (139/1024 : ℝ))) hcmem 8 (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (139/1024 : ℝ)) (990374258611/1000000000000 : ℝ) (495187129307/500000000000 : ℝ) (129158412973/250000000000 : ℝ) (516633651901/1000000000000 : ℝ) (819413707123/1000000000000 : ℝ) (819413707141/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0285_exp_lower
  have heNumeric : (2019010586369/1000000000000 : ℝ)/4 ≤ Real.exp (-10938988454881/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010586369/1000000000000 : ℝ)/4 ≤ Real.exp ((8895/65536 : ℝ)-(819413707141/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8895/65536 : ℝ) (139/1024 : ℝ) (819413707141/1000000000000 : ℝ) (2019010586369/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0286; no trusted numerical premise.
theorem cover7_leaf0286_exp_radius : (249394673996168943/250000000000000000 : ℝ) ≤ Real.exp ((-1271/65536 : ℝ)/8) ∧ Real.exp ((-1271/65536 : ℝ)/8) ≤ (997578695984675773/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1271/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0286_exp_lower : (229522270995529501/250000000000000000 : ℝ) ≤ Real.exp ((-17092170339/25000000000 : ℝ)/8) ∧ Real.exp ((-17092170339/25000000000 : ℝ)/8) ≤ (183617816796423601/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17092170339/25000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0286_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505257721/500000000000 : ℝ) ≤ 4*Real.exp (139/1024 : ℝ)*Real.exp (-mu (radius 7 (8897/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505257721/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8897/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0286_exp_radius
  have hrNumeric : (980792931303/1000000000000 : ℝ) ≤ Real.exp (-1271/65536 : ℝ) ∧ Real.exp (-1271/65536 : ℝ) ≤ (122599116413/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980792931303/1000000000000 : ℝ) ≤ (radius 7 (8897/65536 : ℝ)) ∧ (radius 7 (8897/65536 : ℝ)) ≤ (122599116413/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8897/65536 : ℝ)) (980792931303/1000000000000 : ℝ) (122599116413/125000000000 : ℝ) (97525927199/500000000000 : ℝ) (48762963601/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8897/65536 : ℝ)) (980792931303/1000000000000 : ℝ) (122599116413/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8897/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980792931303/1000000000000 : ℝ) (122599116413/125000000000 : ℝ) (990396465651/1000000000000 : ℝ) (247599116413/250000000000 : ℝ) (990349903469/1000000000000 : ℝ) (990349903471/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8897/65536 : ℝ)) 1 (990396465651/1000000000000 : ℝ) (247599116413/250000000000 : ℝ) (990349903469/1000000000000 : ℝ) (990349903471/1000000000000 : ℝ) (12379664807/12500000000 : ℝ) (495186592281/500000000000 : ℝ) (495186592143/500000000000 : ℝ) (30949162009/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8897/65536 : ℝ)) 2 (12379664807/12500000000 : ℝ) (495186592281/500000000000 : ℝ) (495186592143/500000000000 : ℝ) (30949162009/31250000000 : ℝ) (990373184423/1000000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8897/65536 : ℝ)) 3 (990373184423/1000000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8897/65536 : ℝ)) 4 (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8897/65536 : ℝ)) 5 (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8897/65536 : ℝ)) 6 (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8897/65536 : ℝ)) 7 (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8897/65536 : ℝ))) (97525927199/500000000000 : ℝ) (48762963601/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8897/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97525927199/500000000000 : ℝ) (48762963601/250000000000 : ℝ) (597525927199/1000000000000 : ℝ) (298762963601/500000000000 : ℝ) (441646752957/1000000000000 : ℝ) (88329350593/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8897/65536 : ℝ))) 1 (597525927199/1000000000000 : ℝ) (298762963601/500000000000 : ℝ) (441646752957/1000000000000 : ℝ) (88329350593/200000000000 : ℝ) (259793170039/500000000000 : ℝ) (129896585021/250000000000 : ℝ) (102741498053/200000000000 : ℝ) (16053359071/31250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8897/65536 : ℝ))) 2 (259793170039/500000000000 : ℝ) (129896585021/250000000000 : ℝ) (102741498053/200000000000 : ℝ) (16053359071/31250000000 : ℝ) (516646915171/1000000000000 : ℝ) (258323457589/500000000000 : ℝ) (258319276641/500000000000 : ℝ) (516638553289/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8897/65536 : ℝ))) 3 (516646915171/1000000000000 : ℝ) (258323457589/500000000000 : ℝ) (258319276641/500000000000 : ℝ) (516638553289/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (258321367117/500000000000 : ℝ) (516642734209/1000000000000 : ℝ) (516642734217/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8897/65536 : ℝ))) 4 (258321367113/500000000000 : ℝ) (258321367117/500000000000 : ℝ) (516642734209/1000000000000 : ℝ) (516642734217/1000000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8897/65536 : ℝ))) 5 (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8897/65536 : ℝ))) 6 (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8897/65536 : ℝ))) 7 (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8897/65536 : ℝ)) hmem 8 (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8897/65536 : ℝ))) hcmem 8 (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8897/65536 : ℝ)) (495186592211/500000000000 : ℝ) (39614927377/40000000000 : ℝ) (516642734217/1000000000000 : ℝ) (258321367113/500000000000 : ℝ) (819429001043/1000000000000 : ℝ) (40971450053/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0286_exp_lower
  have heNumeric : (1009505257721/500000000000 : ℝ)/4 ≤ Real.exp (-17092170339/25000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505257721/500000000000 : ℝ)/4 ≤ Real.exp ((139/1024 : ℝ)-(40971450053/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (139/1024 : ℝ) (8897/65536 : ℝ) (40971450053/50000000000 : ℝ) (1009505257721/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0287; no trusted numerical premise.
theorem cover7_leaf0287_exp_radius : (39903136966643587/40000000000000000 : ℝ) ≤ Real.exp ((-4449/229376 : ℝ)/8) ∧ Real.exp ((-4449/229376 : ℝ)/8) ≤ (249394606041522419/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4449/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0287_exp_lower : (918089080081853233/1000000000000000000 : ℝ) ≤ Real.exp ((-2187797912147/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187797912147/3200000000000 : ℝ)/8) ≤ (459044540040926617/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187797912147/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0287_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252376305853/125000000000 : ℝ) ≤ 4*Real.exp (8897/65536 : ℝ)*Real.exp (-mu (radius 7 (4449/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (252376305853/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4449/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0287_exp_radius
  have hrNumeric : (490395396673/500000000000 : ℝ) ≤ Real.exp (-4449/229376 : ℝ) ∧ Real.exp (-4449/229376 : ℝ) ≤ (980790793347/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490395396673/500000000000 : ℝ) ≤ (radius 7 (4449/32768 : ℝ)) ∧ (radius 7 (4449/32768 : ℝ)) ≤ (980790793347/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4449/32768 : ℝ)) (490395396673/500000000000 : ℝ) (980790793347/1000000000000 : ℝ) (195062604529/1000000000000 : ℝ) (39012520907/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4449/32768 : ℝ)) (490395396673/500000000000 : ℝ) (980790793347/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4449/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490395396673/500000000000 : ℝ) (980790793347/1000000000000 : ℝ) (990395396673/1000000000000 : ℝ) (495197698337/500000000000 : ℝ) (495174412037/500000000000 : ℝ) (247587206019/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4449/32768 : ℝ)) 1 (990395396673/1000000000000 : ℝ) (495197698337/500000000000 : ℝ) (495174412037/500000000000 : ℝ) (247587206019/250000000000 : ℝ) (990372110373/1000000000000 : ℝ) (7922976883/8000000000 : ℝ) (990372110099/1000000000000 : ℝ) (495186055051/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4449/32768 : ℝ)) 2 (990372110373/1000000000000 : ℝ) (7922976883/8000000000 : ℝ) (990372110099/1000000000000 : ℝ) (495186055051/500000000000 : ℝ) (247593027559/250000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4449/32768 : ℝ)) 3 (247593027559/250000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4449/32768 : ℝ)) 4 (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4449/32768 : ℝ)) 5 (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4449/32768 : ℝ)) 6 (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4449/32768 : ℝ)) 7 (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4449/32768 : ℝ))) (195062604529/1000000000000 : ℝ) (39012520907/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4449/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195062604529/1000000000000 : ℝ) (39012520907/200000000000 : ℝ) (74691412783/125000000000 : ℝ) (149382825567/250000000000 : ℝ) (220829461649/500000000000 : ℝ) (220829461653/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4449/32768 : ℝ))) 1 (74691412783/125000000000 : ℝ) (149382825567/250000000000 : ℝ) (220829461649/500000000000 : ℝ) (220829461653/500000000000 : ℝ) (519595112781/1000000000000 : ℝ) (519595112787/1000000000000 : ℝ) (513716878829/1000000000000 : ℝ) (513716878837/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4449/32768 : ℝ))) 2 (519595112781/1000000000000 : ℝ) (519595112787/1000000000000 : ℝ) (513716878829/1000000000000 : ℝ) (513716878837/1000000000000 : ℝ) (103331199161/200000000000 : ℝ) (129163998953/250000000000 : ℝ) (258323817907/500000000000 : ℝ) (258323817911/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4449/32768 : ℝ))) 3 (103331199161/200000000000 : ℝ) (129163998953/250000000000 : ℝ) (258323817907/500000000000 : ℝ) (258323817911/500000000000 : ℝ) (516651815809/1000000000000 : ℝ) (516651815817/1000000000000 : ℝ) (32290738487/62500000000 : ℝ) (516651815801/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4449/32768 : ℝ))) 4 (516651815809/1000000000000 : ℝ) (516651815817/1000000000000 : ℝ) (32290738487/62500000000 : ℝ) (516651815801/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4449/32768 : ℝ))) 5 (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4449/32768 : ℝ))) 6 (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4449/32768 : ℝ))) 7 (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4449/32768 : ℝ)) hmem 8 (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4449/32768 : ℝ))) hcmem 8 (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4449/32768 : ℝ)) (198074422047/200000000000 : ℝ) (990372110239/1000000000000 : ℝ) (2583259079/5000000000 : ℝ) (516651815809/1000000000000 : ℝ) (102430536727/125000000000 : ℝ) (163888858767/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0287_exp_lower
  have heNumeric : (252376305853/125000000000 : ℝ)/4 ≤ Real.exp (-2187797912147/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252376305853/125000000000 : ℝ)/4 ≤ Real.exp ((8897/65536 : ℝ)-(163888858767/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8897/65536 : ℝ) (4449/32768 : ℝ) (163888858767/200000000000 : ℝ) (252376305853/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0288; no trusted numerical premise.
theorem cover7_leaf0288_exp_radius : (498789076173788821/500000000000000000 : ℝ) ≤ Real.exp ((-8899/458752 : ℝ)/8) ∧ Real.exp ((-8899/458752 : ℝ)/8) ≤ (997578152347577643/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8899/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0288_exp_lower : (459044538156839273/500000000000000000 : ℝ) ≤ Real.exp ((-5469495043047/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469495043047/8000000000000 : ℝ)/8) ≤ (918089076313678547/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469495043047/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0288_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201901038053/100000000000 : ℝ) ≤ 4*Real.exp (4449/32768 : ℝ)*Real.exp (-mu (radius 7 (8899/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (201901038053/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8899/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0288_exp_radius
  have hrNumeric : (490394327697/500000000000 : ℝ) ≤ Real.exp (-8899/458752 : ℝ) ∧ Real.exp (-8899/458752 : ℝ) ≤ (196157731079/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490394327697/500000000000 : ℝ) ≤ (radius 7 (8899/65536 : ℝ)) ∧ (radius 7 (8899/65536 : ℝ)) ≤ (196157731079/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8899/65536 : ℝ)) (490394327697/500000000000 : ℝ) (196157731079/200000000000 : ℝ) (195073354019/1000000000000 : ℝ) (7802934161/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8899/65536 : ℝ)) (490394327697/500000000000 : ℝ) (196157731079/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8899/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490394327697/500000000000 : ℝ) (196157731079/200000000000 : ℝ) (990394327697/1000000000000 : ℝ) (495197163849/500000000000 : ℝ) (24758693617/25000000000 : ℝ) (495173872341/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8899/65536 : ℝ)) 1 (990394327697/1000000000000 : ℝ) (495197163849/500000000000 : ℝ) (24758693617/25000000000 : ℝ) (495173872341/500000000000 : ℝ) (247592759047/250000000000 : ℝ) (99037103619/100000000000 : ℝ) (495185517957/500000000000 : ℝ) (990371035917/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8899/65536 : ℝ)) 2 (247592759047/250000000000 : ℝ) (99037103619/100000000000 : ℝ) (495185517957/500000000000 : ℝ) (990371035917/1000000000000 : ℝ) (990371036051/1000000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8899/65536 : ℝ)) 3 (990371036051/1000000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8899/65536 : ℝ)) 4 (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8899/65536 : ℝ)) 5 (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8899/65536 : ℝ)) 6 (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8899/65536 : ℝ)) 7 (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8899/65536 : ℝ))) (195073354019/1000000000000 : ℝ) (7802934161/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8899/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195073354019/1000000000000 : ℝ) (7802934161/40000000000 : ℝ) (597536677009/1000000000000 : ℝ) (597536677013/1000000000000 : ℝ) (441671092577/1000000000000 : ℝ) (88334218517/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8899/65536 : ℝ))) 1 (597536677009/1000000000000 : ℝ) (597536677013/1000000000000 : ℝ) (441671092577/1000000000000 : ℝ) (88334218517/200000000000 : ℝ) (519603884793/1000000000000 : ℝ) (519603884799/1000000000000 : ℝ) (256863133297/500000000000 : ℝ) (256863133301/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8899/65536 : ℝ))) 2 (519603884793/1000000000000 : ℝ) (519603884799/1000000000000 : ℝ) (256863133297/500000000000 : ℝ) (256863133301/500000000000 : ℝ) (516665075693/1000000000000 : ℝ) (516665075701/1000000000000 : ℝ) (516656717601/1000000000000 : ℝ) (516656717609/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8899/65536 : ℝ))) 3 (516665075693/1000000000000 : ℝ) (516665075701/1000000000000 : ℝ) (516656717601/1000000000000 : ℝ) (516656717609/1000000000000 : ℝ) (516660896647/1000000000000 : ℝ) (103332179331/200000000000 : ℝ) (51666089663/100000000000 : ℝ) (516660896639/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8899/65536 : ℝ))) 4 (516660896647/1000000000000 : ℝ) (103332179331/200000000000 : ℝ) (51666089663/100000000000 : ℝ) (516660896639/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8899/65536 : ℝ))) 5 (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8899/65536 : ℝ))) 6 (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8899/65536 : ℝ))) 7 (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8899/65536 : ℝ)) hmem 8 (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8899/65536 : ℝ))) hcmem 8 (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8899/65536 : ℝ)) (19807420721/20000000000 : ℝ) (495185518027/500000000000 : ℝ) (258330448319/500000000000 : ℝ) (516660896647/1000000000000 : ℝ) (5121622409/6250000000 : ℝ) (819459585459/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0288_exp_lower
  have heNumeric : (201901038053/100000000000 : ℝ)/4 ≤ Real.exp (-5469495043047/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201901038053/100000000000 : ℝ)/4 ≤ Real.exp ((4449/32768 : ℝ)-(819459585459/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4449/32768 : ℝ) (8899/65536 : ℝ) (819459585459/1000000000000 : ℝ) (201901038053/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0289; no trusted numerical premise.
theorem cover7_leaf0289_exp_radius : (498788940264569837/500000000000000000 : ℝ) ≤ Real.exp ((-2225/114688 : ℝ)/8) ∧ Real.exp ((-2225/114688 : ℝ)/8) ≤ (39903115221165587/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2225/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0289_exp_lower : (183617814535449931/200000000000000000 : ℝ) ≤ Real.exp ((-2187798118617/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187798118617/3200000000000 : ℝ)/8) ≤ (114761134084656207/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187798118617/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0289_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010316553/1000000000000 : ℝ) ≤ 4*Real.exp (8899/65536 : ℝ)*Real.exp (-mu (radius 7 (2225/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010316553/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2225/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0289_exp_radius
  have hrNumeric : (980786517447/1000000000000 : ℝ) ≤ Real.exp (-2225/114688 : ℝ) ∧ Real.exp (-2225/114688 : ℝ) ≤ (122598314681/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980786517447/1000000000000 : ℝ) ≤ (radius 7 (2225/16384 : ℝ)) ∧ (radius 7 (2225/16384 : ℝ)) ≤ (122598314681/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2225/16384 : ℝ)) (980786517447/1000000000000 : ℝ) (122598314681/125000000000 : ℝ) (195084102869/1000000000000 : ℝ) (1560672823/8000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2225/16384 : ℝ)) (980786517447/1000000000000 : ℝ) (122598314681/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2225/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980786517447/1000000000000 : ℝ) (122598314681/125000000000 : ℝ) (990393258723/1000000000000 : ℝ) (247598314681/250000000000 : ℝ) (990346665287/1000000000000 : ℝ) (990346665289/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2225/16384 : ℝ)) 1 (990393258723/1000000000000 : ℝ) (247598314681/250000000000 : ℝ) (990346665287/1000000000000 : ℝ) (990346665289/1000000000000 : ℝ) (198073992401/200000000000 : ℝ) (990369962007/1000000000000 : ℝ) (99036996173/100000000000 : ℝ) (990369961733/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2225/16384 : ℝ)) 2 (198073992401/200000000000 : ℝ) (990369962007/1000000000000 : ℝ) (99036996173/100000000000 : ℝ) (990369961733/1000000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2225/16384 : ℝ)) 3 (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2225/16384 : ℝ)) 4 (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2225/16384 : ℝ)) 5 (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2225/16384 : ℝ)) 6 (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2225/16384 : ℝ)) 7 (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2225/16384 : ℝ))) (195084102869/1000000000000 : ℝ) (1560672823/8000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2225/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195084102869/1000000000000 : ℝ) (1560672823/8000000000 : ℝ) (298771025717/500000000000 : ℝ) (298771025719/500000000000 : ℝ) (441683260797/1000000000000 : ℝ) (88336652161/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2225/16384 : ℝ))) 1 (298771025717/500000000000 : ℝ) (298771025719/500000000000 : ℝ) (441683260797/1000000000000 : ℝ) (88336652161/200000000000 : ℝ) (103922531223/200000000000 : ℝ) (259806328061/500000000000 : ℝ) (513735653561/1000000000000 : ℝ) (513735653569/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2225/16384 : ℝ))) 2 (103922531223/200000000000 : ℝ) (259806328061/500000000000 : ℝ) (513735653561/1000000000000 : ℝ) (513735653569/1000000000000 : ℝ) (258337077419/500000000000 : ℝ) (258337077423/500000000000 : ℝ) (516665798643/1000000000000 : ℝ) (516665798651/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2225/16384 : ℝ))) 3 (258337077419/500000000000 : ℝ) (258337077423/500000000000 : ℝ) (516665798643/1000000000000 : ℝ) (516665798651/1000000000000 : ℝ) (25833498837/50000000000 : ℝ) (516669976749/1000000000000 : ℝ) (516669976723/1000000000000 : ℝ) (129167494183/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2225/16384 : ℝ))) 4 (25833498837/50000000000 : ℝ) (516669976749/1000000000000 : ℝ) (516669976723/1000000000000 : ℝ) (129167494183/250000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2225/16384 : ℝ))) 5 (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2225/16384 : ℝ))) 6 (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2225/16384 : ℝ))) 7 (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2225/16384 : ℝ)) hmem 8 (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2225/16384 : ℝ))) hcmem 8 (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2225/16384 : ℝ)) (990369961867/1000000000000 : ℝ) (99036996187/100000000000 : ℝ) (516669976731/1000000000000 : ℝ) (516669976741/1000000000000 : ℝ) (163894975183/200000000000 : ℝ) (163894975187/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0289_exp_lower
  have heNumeric : (2019010316553/1000000000000 : ℝ)/4 ≤ Real.exp (-2187798118617/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010316553/1000000000000 : ℝ)/4 ≤ Real.exp ((8899/65536 : ℝ)-(163894975187/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8899/65536 : ℝ) (2225/16384 : ℝ) (163894975187/200000000000 : ℝ) (2019010316553/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0290; no trusted numerical premise.
theorem cover7_leaf0290_exp_radius : (99757760871077577/100000000000000000 : ℝ) ≤ Real.exp ((-8901/458752 : ℝ)/8) ∧ Real.exp ((-8901/458752 : ℝ)/8) ≤ (997577608710775771/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8901/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0290_exp_lower : (114761133646656891/125000000000000000 : ℝ) ≤ Real.exp ((-2734747770403/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734747770403/4000000000000 : ℝ)/8) ≤ (918089069173255129/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734747770403/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0290_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010254907/1000000000000 : ℝ) ≤ 4*Real.exp (2225/16384 : ℝ)*Real.exp (-mu (radius 7 (8901/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010254907/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8901/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0290_exp_radius
  have hrNumeric : (196156875901/200000000000 : ℝ) ≤ Real.exp (-8901/458752 : ℝ) ∧ Real.exp (-8901/458752 : ℝ) ≤ (490392189753/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196156875901/200000000000 : ℝ) ≤ (radius 7 (8901/65536 : ℝ)) ∧ (radius 7 (8901/65536 : ℝ)) ≤ (490392189753/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8901/65536 : ℝ)) (196156875901/200000000000 : ℝ) (490392189753/500000000000 : ℝ) (195094851077/1000000000000 : ℝ) (195094851083/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8901/65536 : ℝ)) (196156875901/200000000000 : ℝ) (490392189753/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8901/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196156875901/200000000000 : ℝ) (490392189753/500000000000 : ℝ) (123799023719/125000000000 : ℝ) (990392189753/1000000000000 : ℝ) (123793198237/125000000000 : ℝ) (495172792949/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8901/65536 : ℝ)) 1 (123799023719/125000000000 : ℝ) (990392189753/1000000000000 : ℝ) (123793198237/125000000000 : ℝ) (495172792949/500000000000 : ℝ) (61898055489/62500000000 : ℝ) (495184443913/500000000000 : ℝ) (990368887549/1000000000000 : ℝ) (3868628467/3906250000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8901/65536 : ℝ)) 2 (61898055489/62500000000 : ℝ) (495184443913/500000000000 : ℝ) (990368887549/1000000000000 : ℝ) (3868628467/3906250000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8901/65536 : ℝ)) 3 (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8901/65536 : ℝ)) 4 (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8901/65536 : ℝ)) 5 (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8901/65536 : ℝ)) 6 (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8901/65536 : ℝ)) 7 (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8901/65536 : ℝ))) (195094851077/1000000000000 : ℝ) (195094851083/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8901/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195094851077/1000000000000 : ℝ) (195094851083/1000000000000 : ℝ) (298773712769/500000000000 : ℝ) (298773712771/500000000000 : ℝ) (88339085591/200000000000 : ℝ) (441695427963/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8901/65536 : ℝ))) 1 (298773712769/500000000000 : ℝ) (298773712771/500000000000 : ℝ) (88339085591/200000000000 : ℝ) (441695427963/1000000000000 : ℝ) (259810713373/500000000000 : ℝ) (519621426753/1000000000000 : ℝ) (513745039729/1000000000000 : ℝ) (64218129967/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8901/65536 : ℝ))) 2 (259810713373/500000000000 : ℝ) (519621426753/1000000000000 : ℝ) (513745039729/1000000000000 : ℝ) (64218129967/125000000000 : ℝ) (516683233237/1000000000000 : ℝ) (103336646649/200000000000 : ℝ) (516674878939/1000000000000 : ℝ) (516674878947/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8901/65536 : ℝ))) 3 (516683233237/1000000000000 : ℝ) (103336646649/200000000000 : ℝ) (516674878939/1000000000000 : ℝ) (516674878947/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (16146220503/31250000000 : ℝ) (516679056071/1000000000000 : ℝ) (6458488201/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8901/65536 : ℝ))) 4 (64584882011/125000000000 : ℝ) (16146220503/31250000000 : ℝ) (516679056071/1000000000000 : ℝ) (6458488201/12500000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8901/65536 : ℝ))) 5 (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8901/65536 : ℝ))) 6 (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8901/65536 : ℝ))) 7 (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8901/65536 : ℝ)) hmem 8 (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8901/65536 : ℝ))) hcmem 8 (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8901/65536 : ℝ)) (495184443843/500000000000 : ℝ) (990368887689/1000000000000 : ℝ) (516679056079/1000000000000 : ℝ) (64584882011/125000000000 : ℝ) (819490165239/1000000000000 : ℝ) (819490165257/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0290_exp_lower
  have heNumeric : (2019010254907/1000000000000 : ℝ)/4 ≤ Real.exp (-2734747770403/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010254907/1000000000000 : ℝ)/4 ≤ Real.exp ((2225/16384 : ℝ)-(819490165257/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2225/16384 : ℝ) (8901/65536 : ℝ) (819490165257/1000000000000 : ℝ) (2019010254907/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0291; no trusted numerical premise.
theorem cover7_leaf0291_exp_radius : (997577336892485931/1000000000000000000 : ℝ) ≤ Real.exp ((-4451/229376 : ℝ)/8) ∧ Real.exp ((-4451/229376 : ℝ)/8) ≤ (249394334223121483/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4451/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0291_exp_lower : (114761133224996693/125000000000000000 : ℝ) ≤ Real.exp ((-2187798310383/3200000000000 : ℝ)/8) ∧ Real.exp ((-2187798310383/3200000000000 : ℝ)/8) ≤ (183617813159994709/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2187798310383/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0291_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (50475254889/25000000000 : ℝ) ≤ 4*Real.exp (8901/65536 : ℝ)*Real.exp (-mu (radius 7 (4451/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (50475254889/25000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4451/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0291_exp_radius
  have hrNumeric : (980782241567/1000000000000 : ℝ) ≤ Real.exp (-4451/229376 : ℝ) ∧ Real.exp (-4451/229376 : ℝ) ≤ (30649445049/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980782241567/1000000000000 : ℝ) ≤ (radius 7 (4451/32768 : ℝ)) ∧ (radius 7 (4451/32768 : ℝ)) ≤ (30649445049/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4451/32768 : ℝ)) (980782241567/1000000000000 : ℝ) (30649445049/31250000000 : ℝ) (3902111973/20000000000 : ℝ) (3048524979/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4451/32768 : ℝ)) (980782241567/1000000000000 : ℝ) (30649445049/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4451/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980782241567/1000000000000 : ℝ) (30649445049/31250000000 : ℝ) (990391120783/1000000000000 : ℝ) (61899445049/62500000000 : ℝ) (495172253253/500000000000 : ℝ) (990344506507/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4451/32768 : ℝ)) 1 (990391120783/1000000000000 : ℝ) (61899445049/62500000000 : ℝ) (495172253253/500000000000 : ℝ) (990344506507/1000000000000 : ℝ) (247591953411/250000000000 : ℝ) (495183906823/500000000000 : ℝ) (99036781337/100000000000 : ℝ) (247591953343/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4451/32768 : ℝ)) 2 (247591953411/250000000000 : ℝ) (495183906823/500000000000 : ℝ) (99036781337/100000000000 : ℝ) (247591953343/250000000000 : ℝ) (990367813507/1000000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4451/32768 : ℝ)) 3 (990367813507/1000000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4451/32768 : ℝ)) 4 (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4451/32768 : ℝ)) 5 (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4451/32768 : ℝ)) 6 (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4451/32768 : ℝ)) 7 (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4451/32768 : ℝ))) (3902111973/20000000000 : ℝ) (3048524979/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4451/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3902111973/20000000000 : ℝ) (3048524979/15625000000 : ℝ) (23902111973/40000000000 : ℝ) (18673524979/31250000000 : ℝ) (441707594059/1000000000000 : ℝ) (441707594067/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4451/32768 : ℝ))) 1 (23902111973/40000000000 : ℝ) (18673524979/31250000000 : ℝ) (441707594059/1000000000000 : ℝ) (441707594067/1000000000000 : ℝ) (129907549173/250000000000 : ℝ) (259815098349/500000000000 : ℝ) (513754425103/1000000000000 : ℝ) (51375442511/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4451/32768 : ℝ))) 2 (129907549173/250000000000 : ℝ) (259815098349/500000000000 : ℝ) (513754425103/1000000000000 : ℝ) (51375442511/100000000000 : ℝ) (516692310897/1000000000000 : ℝ) (64586538863/125000000000 : ℝ) (16146373703/31250000000 : ℝ) (64585494813/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4451/32768 : ℝ))) 3 (516692310897/1000000000000 : ℝ) (64586538863/125000000000 : ℝ) (16146373703/31250000000 : ℝ) (64585494813/125000000000 : ℝ) (64586016837/125000000000 : ℝ) (32293008419/62500000000 : ℝ) (516688134679/1000000000000 : ℝ) (16146504209/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4451/32768 : ℝ))) 4 (64586016837/125000000000 : ℝ) (32293008419/62500000000 : ℝ) (516688134679/1000000000000 : ℝ) (16146504209/31250000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4451/32768 : ℝ))) 5 (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4451/32768 : ℝ))) 6 (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4451/32768 : ℝ))) 7 (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4451/32768 : ℝ)) hmem 8 (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4451/32768 : ℝ))) hcmem 8 (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4451/32768 : ℝ)) (495183906753/500000000000 : ℝ) (990367813509/1000000000000 : ℝ) (516688134687/1000000000000 : ℝ) (64586016837/125000000000 : ℝ) (409752726711/500000000000 : ℝ) (1280477271/1562500000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0291_exp_lower
  have heNumeric : (50475254889/25000000000 : ℝ)/4 ≤ Real.exp (-2187798310383/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (50475254889/25000000000 : ℝ)/4 ≤ Real.exp ((8901/65536 : ℝ)-(1280477271/1562500000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8901/65536 : ℝ) (4451/32768 : ℝ) (1280477271/1562500000 : ℝ) (50475254889/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0292; no trusted numerical premise.
theorem cover7_leaf0292_exp_radius : (997577065074270157/1000000000000000000 : ℝ) ≤ Real.exp ((-8903/458752 : ℝ)/8) ∧ Real.exp ((-8903/458752 : ℝ)/8) ≤ (498788532537135079/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8903/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0292_exp_lower : (918089062557863947/1000000000000000000 : ℝ) ≤ Real.exp ((-1093899200393/1600000000000 : ℝ)/8) ∧ Real.exp ((-1093899200393/1600000000000 : ℝ)/8) ≤ (229522265639465987/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1093899200393/1600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0292_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010138521/1000000000000 : ℝ) ≤ 4*Real.exp (4451/32768 : ℝ)*Real.exp (-mu (radius 7 (8903/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010138521/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8903/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0292_exp_radius
  have hrNumeric : (980780103633/1000000000000 : ℝ) ≤ Real.exp (-8903/458752 : ℝ) ∧ Real.exp (-8903/458752 : ℝ) ≤ (490390051817/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980780103633/1000000000000 : ℝ) ≤ (radius 7 (8903/65536 : ℝ)) ∧ (radius 7 (8903/65536 : ℝ)) ≤ (490390051817/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8903/65536 : ℝ)) (980780103633/1000000000000 : ℝ) (490390051817/500000000000 : ℝ) (48779086397/250000000000 : ℝ) (97558172797/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8903/65536 : ℝ)) (980780103633/1000000000000 : ℝ) (490390051817/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8903/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980780103633/1000000000000 : ℝ) (490390051817/500000000000 : ℝ) (123798756477/125000000000 : ℝ) (990390051817/1000000000000 : ℝ) (247585856779/250000000000 : ℝ) (495171713559/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8903/65536 : ℝ)) 1 (123798756477/125000000000 : ℝ) (990390051817/1000000000000 : ℝ) (247585856779/250000000000 : ℝ) (495171713559/500000000000 : ℝ) (495183369733/500000000000 : ℝ) (247591684867/250000000000 : ℝ) (990366739191/1000000000000 : ℝ) (495183369597/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8903/65536 : ℝ)) 2 (495183369733/500000000000 : ℝ) (247591684867/250000000000 : ℝ) (990366739191/1000000000000 : ℝ) (495183369597/500000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8903/65536 : ℝ)) 3 (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8903/65536 : ℝ)) 4 (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8903/65536 : ℝ)) 5 (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8903/65536 : ℝ)) 6 (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8903/65536 : ℝ)) 7 (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8903/65536 : ℝ))) (48779086397/250000000000 : ℝ) (97558172797/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8903/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (48779086397/250000000000 : ℝ) (97558172797/500000000000 : ℝ) (298779086397/500000000000 : ℝ) (597558172797/1000000000000 : ℝ) (441719759109/1000000000000 : ℝ) (441719759117/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8903/65536 : ℝ))) 1 (298779086397/500000000000 : ℝ) (597558172797/1000000000000 : ℝ) (441719759109/1000000000000 : ℝ) (441719759117/1000000000000 : ℝ) (519638965951/1000000000000 : ℝ) (519638965957/1000000000000 : ℝ) (513763809683/1000000000000 : ℝ) (51376380969/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8903/65536 : ℝ))) 2 (519638965951/1000000000000 : ℝ) (519638965957/1000000000000 : ℝ) (513763809683/1000000000000 : ℝ) (51376380969/100000000000 : ℝ) (516701387817/1000000000000 : ℝ) (32293836739/62500000000 : ℝ) (2018332177/3906250000 : ℝ) (516693037319/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8903/65536 : ℝ))) 3 (516701387817/1000000000000 : ℝ) (32293836739/62500000000 : ℝ) (2018332177/3906250000 : ℝ) (516693037319/1000000000000 : ℝ) (129174303141/250000000000 : ℝ) (129174303143/250000000000 : ℝ) (516697212547/1000000000000 : ℝ) (103339442511/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8903/65536 : ℝ))) 4 (129174303141/250000000000 : ℝ) (129174303143/250000000000 : ℝ) (516697212547/1000000000000 : ℝ) (103339442511/200000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8903/65536 : ℝ))) 5 (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8903/65536 : ℝ))) 6 (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8903/65536 : ℝ))) 7 (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8903/65536 : ℝ)) hmem 8 (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8903/65536 : ℝ))) hcmem 8 (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8903/65536 : ℝ)) (7737240151/7812500000 : ℝ) (990366739331/1000000000000 : ℝ) (103339442511/200000000000 : ℝ) (129174303141/250000000000 : ℝ) (819520740463/1000000000000 : ℝ) (1280501157/1562500000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0292_exp_lower
  have heNumeric : (2019010138521/1000000000000 : ℝ)/4 ≤ Real.exp (-1093899200393/1600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010138521/1000000000000 : ℝ)/4 ≤ Real.exp ((4451/32768 : ℝ)-(1280501157/1562500000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4451/32768 : ℝ) (8903/65536 : ℝ) (1280501157/1562500000 : ℝ) (2019010138521/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0293; no trusted numerical premise.
theorem cover7_leaf0293_exp_radius : (997576793256128447/1000000000000000000 : ℝ) ≤ Real.exp ((-159/8192 : ℝ)/8) ∧ Real.exp ((-159/8192 : ℝ)/8) ≤ (15587137394627007/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-159/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0293_exp_lower : (918089059448532993/1000000000000000000 : ℝ) ≤ Real.exp ((-10938992437433/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938992437433/16000000000000 : ℝ)/8) ≤ (459044529724266497/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938992437433/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0293_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009505041909/500000000000 : ℝ) ≤ 4*Real.exp (8903/65536 : ℝ)*Real.exp (-mu (radius 7 (1113/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009505041909/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1113/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0293_exp_radius
  have hrNumeric : (196155593141/200000000000 : ℝ) ≤ Real.exp (-159/8192 : ℝ) ∧ Real.exp (-159/8192 : ℝ) ≤ (490388982853/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196155593141/200000000000 : ℝ) ≤ (radius 7 (1113/8192 : ℝ)) ∧ (radius 7 (1113/8192 : ℝ)) ≤ (490388982853/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1113/8192 : ℝ)) (196155593141/200000000000 : ℝ) (490388982853/500000000000 : ℝ) (4878177297/25000000000 : ℝ) (97563545943/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1113/8192 : ℝ)) (196155593141/200000000000 : ℝ) (490388982853/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1113/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196155593141/200000000000 : ℝ) (490388982853/500000000000 : ℝ) (247597245713/250000000000 : ℝ) (990388982853/1000000000000 : ℝ) (61896396733/62500000000 : ℝ) (99034234773/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1113/8192 : ℝ)) 1 (247597245713/250000000000 : ℝ) (990388982853/1000000000000 : ℝ) (61896396733/62500000000 : ℝ) (99034234773/100000000000 : ℝ) (99036566529/100000000000 : ℝ) (247591416323/250000000000 : ℝ) (198073133003/200000000000 : ℝ) (495182832509/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1113/8192 : ℝ)) 2 (99036566529/100000000000 : ℝ) (247591416323/250000000000 : ℝ) (198073133003/200000000000 : ℝ) (495182832509/500000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1113/8192 : ℝ)) 3 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1113/8192 : ℝ)) 4 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1113/8192 : ℝ)) 5 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1113/8192 : ℝ)) 6 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1113/8192 : ℝ)) 7 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1113/8192 : ℝ))) (4878177297/25000000000 : ℝ) (97563545943/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1113/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4878177297/25000000000 : ℝ) (97563545943/500000000000 : ℝ) (29878177297/50000000000 : ℝ) (597563545943/1000000000000 : ℝ) (441731923093/1000000000000 : ℝ) (441731923101/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1113/8192 : ℝ))) 1 (29878177297/50000000000 : ℝ) (597563545943/1000000000000 : ℝ) (441731923093/1000000000000 : ℝ) (441731923101/1000000000000 : ℝ) (129911933629/250000000000 : ℝ) (259823867261/500000000000 : ℝ) (25688659673/50000000000 : ℝ) (513773193467/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1113/8192 : ℝ))) 2 (129911933629/250000000000 : ℝ) (259823867261/500000000000 : ℝ) (25688659673/50000000000 : ℝ) (513773193467/1000000000000 : ℝ) (129177615997/250000000000 : ℝ) (103342092799/200000000000 : ℝ) (258351057689/500000000000 : ℝ) (103340423077/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1113/8192 : ℝ))) 3 (129177615997/250000000000 : ℝ) (103342092799/200000000000 : ℝ) (258351057689/500000000000 : ℝ) (103340423077/200000000000 : ℝ) (516706289683/1000000000000 : ℝ) (51670628969/100000000000 : ℝ) (258353144833/500000000000 : ℝ) (258353144837/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1113/8192 : ℝ))) 4 (516706289683/1000000000000 : ℝ) (51670628969/100000000000 : ℝ) (258353144833/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1113/8192 : ℝ))) 5 (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1113/8192 : ℝ))) 6 (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1113/8192 : ℝ))) 7 (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1113/8192 : ℝ)) hmem 8 (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1113/8192 : ℝ))) hcmem 8 (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1113/8192 : ℝ)) (7737231759/7812500000 : ℝ) (198073133031/200000000000 : ℝ) (258353144837/500000000000 : ℝ) (258353144841/500000000000 : ℝ) (819536026347/1000000000000 : ℝ) (819536026363/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0293_exp_lower
  have heNumeric : (1009505041909/500000000000 : ℝ)/4 ≤ Real.exp (-10938992437433/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009505041909/500000000000 : ℝ)/4 ≤ Real.exp ((8903/65536 : ℝ)-(819536026363/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8903/65536 : ℝ) (1113/8192 : ℝ) (819536026363/1000000000000 : ℝ) (1009505041909/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0294; no trusted numerical premise.
theorem cover7_leaf0294_exp_radius : (498788260719030401/500000000000000000 : ℝ) ≤ Real.exp ((-8905/458752 : ℝ)/8) ∧ Real.exp ((-8905/458752 : ℝ)/8) ≤ (997576521438060803/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8905/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0294_exp_lower : (918089056470259261/1000000000000000000 : ℝ) ≤ Real.exp ((-1367374106583/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367374106583/2000000000000 : ℝ)/8) ≤ (459044528235129631/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367374106583/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0294_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019010031421/1000000000000 : ℝ) ≤ 4*Real.exp (1113/8192 : ℝ)*Real.exp (-mu (radius 7 (8905/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (2019010031421/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8905/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0294_exp_radius
  have hrNumeric : (980775827781/1000000000000 : ℝ) ≤ Real.exp (-8905/458752 : ℝ) ∧ Real.exp (-8905/458752 : ℝ) ≤ (490387913891/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980775827781/1000000000000 : ℝ) ≤ (radius 7 (8905/65536 : ℝ)) ∧ (radius 7 (8905/65536 : ℝ)) ≤ (490387913891/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8905/65536 : ℝ)) (980775827781/1000000000000 : ℝ) (490387913891/500000000000 : ℝ) (6098057423/31250000000 : ℝ) (97568918771/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8905/65536 : ℝ)) (980775827781/1000000000000 : ℝ) (490387913891/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8905/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980775827781/1000000000000 : ℝ) (490387913891/500000000000 : ℝ) (99038791389/100000000000 : ℝ) (990387913891/1000000000000 : ℝ) (990341268341/1000000000000 : ℝ) (990341268343/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8905/65536 : ℝ)) 1 (99038791389/100000000000 : ℝ) (990387913891/1000000000000 : ℝ) (990341268341/1000000000000 : ℝ) (990341268343/1000000000000 : ℝ) (198072918223/200000000000 : ℝ) (990364591117/1000000000000 : ℝ) (24759114771/25000000000 : ℝ) (990364590843/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8905/65536 : ℝ)) 2 (198072918223/200000000000 : ℝ) (990364591117/1000000000000 : ℝ) (24759114771/25000000000 : ℝ) (990364590843/1000000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8905/65536 : ℝ)) 3 (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8905/65536 : ℝ)) 4 (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8905/65536 : ℝ)) 5 (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8905/65536 : ℝ)) 6 (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8905/65536 : ℝ)) 7 (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8905/65536 : ℝ))) (6098057423/31250000000 : ℝ) (97568918771/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8905/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (6098057423/31250000000 : ℝ) (97568918771/500000000000 : ℝ) (37348057423/62500000000 : ℝ) (597568918771/1000000000000 : ℝ) (220872043011/500000000000 : ℝ) (44174408603/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8905/65536 : ℝ))) 1 (37348057423/62500000000 : ℝ) (597568918771/1000000000000 : ℝ) (220872043011/500000000000 : ℝ) (44174408603/100000000000 : ℝ) (103931300479/200000000000 : ℝ) (519656502401/1000000000000 : ℝ) (256891288221/500000000000 : ℝ) (513782576449/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8905/65536 : ℝ))) 2 (103931300479/200000000000 : ℝ) (519656502401/1000000000000 : ℝ) (256891288221/500000000000 : ℝ) (513782576449/1000000000000 : ℝ) (258359769709/500000000000 : ℝ) (20668781577/40000000000 : ℝ) (516711192703/1000000000000 : ℝ) (516711192711/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8905/65536 : ℝ))) 3 (258359769709/500000000000 : ℝ) (20668781577/40000000000 : ℝ) (516711192703/1000000000000 : ℝ) (516711192711/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (129178841517/250000000000 : ℝ) (516715366043/1000000000000 : ℝ) (129178841513/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8905/65536 : ℝ))) 4 (25835768303/50000000000 : ℝ) (129178841517/250000000000 : ℝ) (516715366043/1000000000000 : ℝ) (129178841513/250000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8905/65536 : ℝ))) 5 (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8905/65536 : ℝ))) 6 (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8905/65536 : ℝ))) 7 (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8905/65536 : ℝ)) hmem 8 (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8905/65536 : ℝ))) hcmem 8 (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8905/65536 : ℝ)) (990364590977/1000000000000 : ℝ) (49518229549/50000000000 : ℝ) (516715366051/1000000000000 : ℝ) (25835768303/50000000000 : ℝ) (409775655543/500000000000 : ℝ) (3201372309/3906250000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0294_exp_lower
  have heNumeric : (2019010031421/1000000000000 : ℝ)/4 ≤ Real.exp (-1367374106583/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019010031421/1000000000000 : ℝ)/4 ≤ Real.exp ((1113/8192 : ℝ)-(3201372309/3906250000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1113/8192 : ℝ) (8905/65536 : ℝ) (3201372309/3906250000 : ℝ) (2019010031421/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0295; no trusted numerical premise.
theorem cover7_leaf0295_exp_radius : (997576249620067221/1000000000000000000 : ℝ) ≤ Real.exp ((-4453/229376 : ℝ)/8) ∧ Real.exp ((-4453/229376 : ℝ)/8) ≤ (498788124810033611/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4453/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0295_exp_lower : (229522263405674617/250000000000000000 : ℝ) ≤ Real.exp ((-10938993249671/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938993249671/16000000000000 : ℝ)/8) ≤ (918089053622698469/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938993249671/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0295_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504752495331/250000000000 : ℝ) ≤ 4*Real.exp (8905/65536 : ℝ)*Real.exp (-mu (radius 7 (4453/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (504752495331/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4453/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0295_exp_radius
  have hrNumeric : (980773689861/1000000000000 : ℝ) ≤ Real.exp (-4453/229376 : ℝ) ∧ Real.exp (-4453/229376 : ℝ) ≤ (490386844931/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980773689861/1000000000000 : ℝ) ≤ (radius 7 (4453/32768 : ℝ)) ∧ (radius 7 (4453/32768 : ℝ)) ≤ (490386844931/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4453/32768 : ℝ)) (980773689861/1000000000000 : ℝ) (490386844931/500000000000 : ℝ) (97574291279/500000000000 : ℝ) (48787145641/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4453/32768 : ℝ)) (980773689861/1000000000000 : ℝ) (490386844931/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4453/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980773689861/1000000000000 : ℝ) (490386844931/500000000000 : ℝ) (99038684493/100000000000 : ℝ) (990386844931/1000000000000 : ℝ) (198068037791/200000000000 : ℝ) (990340188957/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4453/32768 : ℝ)) 1 (99038684493/100000000000 : ℝ) (990386844931/1000000000000 : ℝ) (198068037791/200000000000 : ℝ) (990340188957/1000000000000 : ℝ) (495181758471/500000000000 : ℝ) (61897719809/62500000000 : ℝ) (990363516667/1000000000000 : ℝ) (99036351667/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4453/32768 : ℝ)) 2 (495181758471/500000000000 : ℝ) (61897719809/62500000000 : ℝ) (990363516667/1000000000000 : ℝ) (99036351667/100000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4453/32768 : ℝ)) 3 (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4453/32768 : ℝ)) 4 (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4453/32768 : ℝ)) 5 (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4453/32768 : ℝ)) 6 (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4453/32768 : ℝ)) 7 (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4453/32768 : ℝ))) (97574291279/500000000000 : ℝ) (48787145641/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4453/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97574291279/500000000000 : ℝ) (48787145641/250000000000 : ℝ) (597574291279/1000000000000 : ℝ) (298787145641/500000000000 : ℝ) (441756247899/1000000000000 : ℝ) (441756247907/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4453/32768 : ℝ))) 1 (597574291279/1000000000000 : ℝ) (298787145641/500000000000 : ℝ) (441756247899/1000000000000 : ℝ) (441756247907/1000000000000 : ℝ) (519665269589/1000000000000 : ℝ) (103933053919/200000000000 : ℝ) (513791958633/1000000000000 : ℝ) (6422399483/12500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4453/32768 : ℝ))) 2 (519665269589/1000000000000 : ℝ) (103933053919/200000000000 : ℝ) (513791958633/1000000000000 : ℝ) (6422399483/12500000000 : ℝ) (516728614111/1000000000000 : ℝ) (258364307059/500000000000 : ℝ) (51672026929/100000000000 : ℝ) (258360134649/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4453/32768 : ℝ))) 3 (516728614111/1000000000000 : ℝ) (258364307059/500000000000 : ℝ) (51672026929/100000000000 : ℝ) (258360134649/500000000000 : ℝ) (5167244417/10000000000 : ℝ) (129181110427/250000000000 : ℝ) (516724441683/1000000000000 : ℝ) (129181110423/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4453/32768 : ℝ))) 4 (5167244417/10000000000 : ℝ) (129181110427/250000000000 : ℝ) (516724441683/1000000000000 : ℝ) (129181110423/250000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4453/32768 : ℝ))) 5 (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4453/32768 : ℝ))) 6 (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4453/32768 : ℝ))) 7 (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4453/32768 : ℝ)) hmem 8 (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4453/32768 : ℝ))) hcmem 8 (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4453/32768 : ℝ)) (247590879201/250000000000 : ℝ) (990363516807/1000000000000 : ℝ) (516724441691/1000000000000 : ℝ) (5167244417/10000000000 : ℝ) (6402864021/7812500000 : ℝ) (409783297353/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0295_exp_lower
  have heNumeric : (504752495331/250000000000 : ℝ)/4 ≤ Real.exp (-10938993249671/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504752495331/250000000000 : ℝ)/4 ≤ Real.exp ((8905/65536 : ℝ)-(409783297353/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8905/65536 : ℝ) (4453/32768 : ℝ) (409783297353/500000000000 : ℝ) (504752495331/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0296; no trusted numerical premise.
theorem cover7_leaf0296_exp_radius : (199515195560429541/200000000000000000 : ℝ) ≤ Real.exp ((-8907/458752 : ℝ)/8) ∧ Real.exp ((-8907/458752 : ℝ)/8) ≤ (498787988901073853/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8907/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0296_exp_lower : (229522262727036459/250000000000000000 : ℝ) ≤ Real.exp ((-5469496814067/8000000000000 : ℝ)/8) ∧ Real.exp ((-5469496814067/8000000000000 : ℝ)/8) ≤ (918089050908145837/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5469496814067/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0296_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009504966783/500000000000 : ℝ) ≤ 4*Real.exp (4453/32768 : ℝ)*Real.exp (-mu (radius 7 (8907/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (1009504966783/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8907/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0296_exp_radius
  have hrNumeric : (980771551947/1000000000000 : ℝ) ≤ Real.exp (-8907/458752 : ℝ) ∧ Real.exp (-8907/458752 : ℝ) ≤ (245192887987/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980771551947/1000000000000 : ℝ) ≤ (radius 7 (8907/65536 : ℝ)) ∧ (radius 7 (8907/65536 : ℝ)) ≤ (245192887987/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8907/65536 : ℝ)) (980771551947/1000000000000 : ℝ) (245192887987/250000000000 : ℝ) (97579663467/500000000000 : ℝ) (9757966347/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8907/65536 : ℝ)) (980771551947/1000000000000 : ℝ) (245192887987/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8907/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980771551947/1000000000000 : ℝ) (245192887987/250000000000 : ℝ) (990385775973/1000000000000 : ℝ) (495192887987/500000000000 : ℝ) (990339109571/1000000000000 : ℝ) (990339109573/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8907/65536 : ℝ)) 1 (990385775973/1000000000000 : ℝ) (495192887987/500000000000 : ℝ) (990339109571/1000000000000 : ℝ) (990339109573/1000000000000 : ℝ) (247590610693/250000000000 : ℝ) (495181221387/500000000000 : ℝ) (990362442497/1000000000000 : ℝ) (990362442499/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8907/65536 : ℝ)) 2 (247590610693/250000000000 : ℝ) (495181221387/500000000000 : ℝ) (990362442497/1000000000000 : ℝ) (990362442499/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8907/65536 : ℝ)) 3 (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8907/65536 : ℝ)) 4 (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8907/65536 : ℝ)) 5 (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8907/65536 : ℝ)) 6 (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8907/65536 : ℝ)) 7 (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8907/65536 : ℝ))) (97579663467/500000000000 : ℝ) (9757966347/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8907/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97579663467/500000000000 : ℝ) (9757966347/50000000000 : ℝ) (597579663467/1000000000000 : ℝ) (59757966347/100000000000 : ℝ) (441768408709/1000000000000 : ℝ) (441768408717/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8907/65536 : ℝ))) 1 (597579663467/1000000000000 : ℝ) (59757966347/100000000000 : ℝ) (441768408709/1000000000000 : ℝ) (441768408717/1000000000000 : ℝ) (64959254511/125000000000 : ℝ) (259837018047/500000000000 : ℝ) (25690067001/50000000000 : ℝ) (513801340027/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8907/65536 : ℝ))) 2 (64959254511/125000000000 : ℝ) (259837018047/500000000000 : ℝ) (25690067001/50000000000 : ℝ) (513801340027/1000000000000 : ℝ) (258368844027/500000000000 : ℝ) (516737688061/1000000000000 : ℝ) (516729345127/1000000000000 : ℝ) (258364672567/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8907/65536 : ℝ))) 3 (258368844027/500000000000 : ℝ) (516737688061/1000000000000 : ℝ) (516729345127/1000000000000 : ℝ) (258364672567/500000000000 : ℝ) (51673351659/100000000000 : ℝ) (258366758299/500000000000 : ℝ) (516733516573/1000000000000 : ℝ) (516733516581/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8907/65536 : ℝ))) 4 (51673351659/100000000000 : ℝ) (258366758299/500000000000 : ℝ) (516733516573/1000000000000 : ℝ) (516733516581/1000000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8907/65536 : ℝ))) 5 (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8907/65536 : ℝ))) 6 (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8907/65536 : ℝ))) 7 (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8907/65536 : ℝ)) hmem 8 (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8907/65536 : ℝ))) hcmem 8 (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8907/65536 : ℝ)) (495181221317/500000000000 : ℝ) (990362442637/1000000000000 : ℝ) (516733516581/1000000000000 : ℝ) (51673351659/100000000000 : ℝ) (819581877131/1000000000000 : ℝ) (819581877149/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0296_exp_lower
  have heNumeric : (1009504966783/500000000000 : ℝ)/4 ≤ Real.exp (-5469496814067/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009504966783/500000000000 : ℝ)/4 ≤ Real.exp ((4453/32768 : ℝ)-(819581877149/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (4453/32768 : ℝ) (8907/65536 : ℝ) (819581877149/1000000000000 : ℝ) (1009504966783/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0297; no trusted numerical premise.
theorem cover7_leaf0297_exp_radius : (997575705984302253/1000000000000000000 : ℝ) ≤ Real.exp ((-2227/114688 : ℝ)/8) ∧ Real.exp ((-2227/114688 : ℝ)/8) ≤ (498787852992151127/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2227/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0297_exp_lower : (459044524162267831/500000000000000000 : ℝ) ≤ Real.exp ((-10938993988341/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938993988341/16000000000000 : ℝ)/8) ≤ (918089048324535663/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938993988341/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0297_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (126188118007/62500000000 : ℝ) ≤ 4*Real.exp (8907/65536 : ℝ)*Real.exp (-mu (radius 7 (2227/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (126188118007/62500000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2227/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0297_exp_radius
  have hrNumeric : (980769414037/1000000000000 : ℝ) ≤ Real.exp (-2227/114688 : ℝ) ∧ Real.exp (-2227/114688 : ℝ) ≤ (490384707019/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980769414037/1000000000000 : ℝ) ≤ (radius 7 (2227/16384 : ℝ)) ∧ (radius 7 (2227/16384 : ℝ)) ≤ (490384707019/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2227/16384 : ℝ)) (980769414037/1000000000000 : ℝ) (490384707019/500000000000 : ℝ) (7806802827/40000000000 : ℝ) (195170070681/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2227/16384 : ℝ)) (980769414037/1000000000000 : ℝ) (490384707019/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2227/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980769414037/1000000000000 : ℝ) (490384707019/500000000000 : ℝ) (495192353509/500000000000 : ℝ) (990384707019/1000000000000 : ℝ) (247584507547/250000000000 : ℝ) (990338030189/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2227/16384 : ℝ)) 1 (495192353509/500000000000 : ℝ) (990384707019/1000000000000 : ℝ) (247584507547/250000000000 : ℝ) (990338030189/1000000000000 : ℝ) (990361368603/1000000000000 : ℝ) (247590342151/250000000000 : ℝ) (123795171041/125000000000 : ℝ) (99036136833/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2227/16384 : ℝ)) 2 (990361368603/1000000000000 : ℝ) (247590342151/250000000000 : ℝ) (123795171041/125000000000 : ℝ) (99036136833/100000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2227/16384 : ℝ)) 3 (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2227/16384 : ℝ)) 4 (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2227/16384 : ℝ)) 5 (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2227/16384 : ℝ)) 6 (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2227/16384 : ℝ)) 7 (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2227/16384 : ℝ))) (7806802827/40000000000 : ℝ) (195170070681/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2227/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7806802827/40000000000 : ℝ) (195170070681/1000000000000 : ℝ) (597585035337/1000000000000 : ℝ) (597585035341/1000000000000 : ℝ) (220890284233/500000000000 : ℝ) (220890284237/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2227/16384 : ℝ))) 1 (597585035337/1000000000000 : ℝ) (597585035341/1000000000000 : ℝ) (220890284233/500000000000 : ℝ) (220890284237/500000000000 : ℝ) (519682801901/1000000000000 : ℝ) (129920700477/250000000000 : ℝ) (256905360307/500000000000 : ℝ) (513810720621/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2227/16384 : ℝ))) 2 (519682801901/1000000000000 : ℝ) (129920700477/250000000000 : ℝ) (256905360307/500000000000 : ℝ) (513810720621/1000000000000 : ℝ) (516746761257/1000000000000 : ℝ) (103349352253/200000000000 : ℝ) (516738420223/1000000000000 : ℝ) (516738420231/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2227/16384 : ℝ))) 3 (516746761257/1000000000000 : ℝ) (103349352253/200000000000 : ℝ) (516738420223/1000000000000 : ℝ) (516738420231/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (129185647687/250000000000 : ℝ) (516742590723/1000000000000 : ℝ) (129185647683/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2227/16384 : ℝ))) 4 (25837129537/50000000000 : ℝ) (129185647687/250000000000 : ℝ) (516742590723/1000000000000 : ℝ) (129185647683/250000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2227/16384 : ℝ))) 5 (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2227/16384 : ℝ))) 6 (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2227/16384 : ℝ))) 7 (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2227/16384 : ℝ)) hmem 8 (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2227/16384 : ℝ))) hcmem 8 (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2227/16384 : ℝ)) (198072273693/200000000000 : ℝ) (990361368467/1000000000000 : ℝ) (516742590731/1000000000000 : ℝ) (25837129537/50000000000 : ℝ) (409798579217/500000000000 : ℝ) (819597158451/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0297_exp_lower
  have heNumeric : (126188118007/62500000000 : ℝ)/4 ≤ Real.exp (-10938993988341/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (126188118007/62500000000 : ℝ)/4 ≤ Real.exp ((8907/65536 : ℝ)-(819597158451/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8907/65536 : ℝ) (2227/16384 : ℝ) (819597158451/1000000000000 : ℝ) (126188118007/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0298; no trusted numerical premise.
theorem cover7_leaf0298_exp_radius : (498787717083265433/500000000000000000 : ℝ) ≤ Real.exp ((-8909/458752 : ℝ)/8) ∧ Real.exp ((-8909/458752 : ℝ)/8) ≤ (997575434166530867/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8909/458752 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0298_exp_lower : (918089045871523661/1000000000000000000 : ℝ) ≤ Real.exp ((-546949716517/800000000000 : ℝ)/8) ∧ Real.exp ((-546949716517/800000000000 : ℝ)/8) ≤ (459044522935761831/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546949716517/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0298_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504752461239/250000000000 : ℝ) ≤ 4*Real.exp (2227/16384 : ℝ)*Real.exp (-mu (radius 7 (8909/65536 : ℝ))) ∧ (2019/1000 : ℝ) < (504752461239/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (8909/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0298_exp_radius
  have hrNumeric : (980767276131/1000000000000 : ℝ) ≤ Real.exp (-8909/458752 : ℝ) ∧ Real.exp (-8909/458752 : ℝ) ≤ (245191819033/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980767276131/1000000000000 : ℝ) ≤ (radius 7 (8909/65536 : ℝ)) ∧ (radius 7 (8909/65536 : ℝ)) ≤ (245191819033/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (8909/65536 : ℝ)) (980767276131/1000000000000 : ℝ) (245191819033/250000000000 : ℝ) (97590406891/500000000000 : ℝ) (48795203447/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (8909/65536 : ℝ)) (980767276131/1000000000000 : ℝ) (245191819033/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (8909/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980767276131/1000000000000 : ℝ) (245191819033/250000000000 : ℝ) (198076727613/200000000000 : ℝ) (495191819033/500000000000 : ℝ) (198067390161/200000000000 : ℝ) (990336950807/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (8909/65536 : ℝ)) 1 (198076727613/200000000000 : ℝ) (495191819033/500000000000 : ℝ) (198067390161/200000000000 : ℝ) (990336950807/1000000000000 : ℝ) (198072058887/200000000000 : ℝ) (990360294437/1000000000000 : ℝ) (990360294159/1000000000000 : ℝ) (495180147081/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (8909/65536 : ℝ)) 2 (198072058887/200000000000 : ℝ) (990360294437/1000000000000 : ℝ) (990360294159/1000000000000 : ℝ) (495180147081/500000000000 : ℝ) (990360294297/1000000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (8909/65536 : ℝ)) 3 (990360294297/1000000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (8909/65536 : ℝ)) 4 (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (8909/65536 : ℝ)) 5 (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (8909/65536 : ℝ)) 6 (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (8909/65536 : ℝ)) 7 (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (8909/65536 : ℝ))) (97590406891/500000000000 : ℝ) (48795203447/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (8909/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (97590406891/500000000000 : ℝ) (48795203447/250000000000 : ℝ) (597590406891/1000000000000 : ℝ) (298795203447/500000000000 : ℝ) (441792727171/1000000000000 : ℝ) (441792727179/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (8909/65536 : ℝ))) 1 (597590406891/1000000000000 : ℝ) (298795203447/500000000000 : ℝ) (441792727171/1000000000000 : ℝ) (441792727179/1000000000000 : ℝ) (519691567031/1000000000000 : ℝ) (519691567037/1000000000000 : ℝ) (8028439069/15625000000 : ℝ) (513820100423/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (8909/65536 : ℝ))) 2 (519691567031/1000000000000 : ℝ) (519691567037/1000000000000 : ℝ) (8028439069/15625000000 : ℝ) (513820100423/1000000000000 : ℝ) (516755833723/1000000000000 : ℝ) (51675583373/100000000000 : ℝ) (258373747291/500000000000 : ℝ) (516747494589/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (8909/65536 : ℝ))) 3 (516755833723/1000000000000 : ℝ) (51675583373/100000000000 : ℝ) (258373747291/500000000000 : ℝ) (516747494589/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (3229697901/6250000000 : ℝ) (103350332827/200000000000 : ℝ) (516751664143/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (8909/65536 : ℝ))) 4 (64593958019/125000000000 : ℝ) (3229697901/6250000000 : ℝ) (103350332827/200000000000 : ℝ) (516751664143/1000000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (8909/65536 : ℝ))) 5 (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (8909/65536 : ℝ))) 6 (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (8909/65536 : ℝ))) 7 (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (8909/65536 : ℝ)) hmem 8 (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (8909/65536 : ℝ))) hcmem 8 (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (8909/65536 : ℝ)) (123795036787/125000000000 : ℝ) (9903602943/10000000000 : ℝ) (516751664143/1000000000000 : ℝ) (64593958019/125000000000 : ℝ) (819612438597/1000000000000 : ℝ) (163922487723/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0298_exp_lower
  have heNumeric : (504752461239/250000000000 : ℝ)/4 ≤ Real.exp (-546949716517/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504752461239/250000000000 : ℝ)/4 ≤ Real.exp ((2227/16384 : ℝ)-(163922487723/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2227/16384 : ℝ) (8909/65536 : ℝ) (163922487723/200000000000 : ℝ) (504752461239/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0299; no trusted numerical premise.
theorem cover7_leaf0299_exp_radius : (997575162348833543/1000000000000000000 : ℝ) ≤ Real.exp ((-4455/229376 : ℝ)/8) ∧ Real.exp ((-4455/229376 : ℝ)/8) ≤ (124696895293604193/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4455/229376 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0299_exp_lower : (918089043551405057/1000000000000000000 : ℝ) ≤ Real.exp ((-10938994653811/16000000000000 : ℝ)/8) ∧ Real.exp ((-10938994653811/16000000000000 : ℝ)/8) ≤ (459044521775702529/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10938994653811/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0299_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009504902069/500000000000 : ℝ) ≤ 4*Real.exp (8909/65536 : ℝ)*Real.exp (-mu (radius 7 (4455/32768 : ℝ))) ∧ (2019/1000 : ℝ) < (1009504902069/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (4455/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0299_exp_radius
  have hrNumeric : (980765138231/1000000000000 : ℝ) ≤ Real.exp (-4455/229376 : ℝ) ∧ Real.exp (-4455/229376 : ℝ) ≤ (122595642279/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (980765138231/1000000000000 : ℝ) ≤ (radius 7 (4455/32768 : ℝ)) ∧ (radius 7 (4455/32768 : ℝ)) ≤ (122595642279/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (4455/32768 : ℝ)) (980765138231/1000000000000 : ℝ) (122595642279/125000000000 : ℝ) (195191556243/1000000000000 : ℝ) (195191556249/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (4455/32768 : ℝ)) (980765138231/1000000000000 : ℝ) (122595642279/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (4455/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (980765138231/1000000000000 : ℝ) (122595642279/125000000000 : ℝ) (198076513823/200000000000 : ℝ) (247595642279/250000000000 : ℝ) (15473997991/15625000000 : ℝ) (495167935713/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (4455/32768 : ℝ)) 1 (198076513823/200000000000 : ℝ) (247595642279/250000000000 : ℝ) (15473997991/15625000000 : ℝ) (495167935713/500000000000 : ℝ) (990359220269/1000000000000 : ℝ) (990359220271/1000000000000 : ℝ) (495179609997/500000000000 : ℝ) (247589804999/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (4455/32768 : ℝ)) 2 (990359220269/1000000000000 : ℝ) (990359220271/1000000000000 : ℝ) (495179609997/500000000000 : ℝ) (247589804999/250000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (4455/32768 : ℝ)) 3 (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (4455/32768 : ℝ)) 4 (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (4455/32768 : ℝ)) 5 (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (4455/32768 : ℝ)) 6 (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (4455/32768 : ℝ)) 7 (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (4455/32768 : ℝ))) (195191556243/1000000000000 : ℝ) (195191556249/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (4455/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (195191556243/1000000000000 : ℝ) (195191556249/1000000000000 : ℝ) (597595778121/1000000000000 : ℝ) (191230649/320000000 : ℝ) (441804884811/1000000000000 : ℝ) (220902442409/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (4455/32768 : ℝ))) 1 (597595778121/1000000000000 : ℝ) (191230649/320000000 : ℝ) (441804884811/1000000000000 : ℝ) (220902442409/500000000000 : ℝ) (259850165733/500000000000 : ℝ) (32481270717/62500000000 : ℝ) (102765895883/200000000000 : ℝ) (256914739711/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (4455/32768 : ℝ))) 2 (259850165733/500000000000 : ℝ) (32481270717/62500000000 : ℝ) (102765895883/200000000000 : ℝ) (256914739711/500000000000 : ℝ) (3229780659/6250000000 : ℝ) (516764905447/1000000000000 : ℝ) (516756568191/1000000000000 : ℝ) (258378284099/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (4455/32768 : ℝ))) 3 (3229780659/6250000000 : ℝ) (516764905447/1000000000000 : ℝ) (516756568191/1000000000000 : ℝ) (258378284099/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (516760736823/1000000000000 : ℝ) (258380368399/500000000000 : ℝ) (258380368403/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (4455/32768 : ℝ))) 4 (103352147363/200000000000 : ℝ) (516760736823/1000000000000 : ℝ) (258380368399/500000000000 : ℝ) (258380368403/500000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (4455/32768 : ℝ))) 5 (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (4455/32768 : ℝ))) 6 (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (4455/32768 : ℝ))) 7 (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (4455/32768 : ℝ)) hmem 8 (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (4455/32768 : ℝ))) hcmem 8 (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (4455/32768 : ℝ)) (990359220131/1000000000000 : ℝ) (495179610067/500000000000 : ℝ) (258380368403/500000000000 : ℝ) (103352147363/200000000000 : ℝ) (204906929401/250000000000 : ℝ) (819627717621/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0299_exp_lower
  have heNumeric : (1009504902069/500000000000 : ℝ)/4 ≤ Real.exp (-10938994653811/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009504902069/500000000000 : ℝ)/4 ≤ Real.exp ((8909/65536 : ℝ)-(819627717621/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (8909/65536 : ℝ) (4455/32768 : ℝ) (819627717621/1000000000000 : ℝ) (1009504902069/500000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0275_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0275_certificate
#check SmaleRate.Proofs.cover7_leaf0276_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0276_certificate
#check SmaleRate.Proofs.cover7_leaf0277_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0277_certificate
#check SmaleRate.Proofs.cover7_leaf0278_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0278_certificate
#check SmaleRate.Proofs.cover7_leaf0279_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0279_certificate
#check SmaleRate.Proofs.cover7_leaf0280_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0280_certificate
#check SmaleRate.Proofs.cover7_leaf0281_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0281_certificate
#check SmaleRate.Proofs.cover7_leaf0282_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0282_certificate
#check SmaleRate.Proofs.cover7_leaf0283_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0283_certificate
#check SmaleRate.Proofs.cover7_leaf0284_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0284_certificate
#check SmaleRate.Proofs.cover7_leaf0285_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0285_certificate
#check SmaleRate.Proofs.cover7_leaf0286_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0286_certificate
#check SmaleRate.Proofs.cover7_leaf0287_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0287_certificate
#check SmaleRate.Proofs.cover7_leaf0288_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0288_certificate
#check SmaleRate.Proofs.cover7_leaf0289_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0289_certificate
#check SmaleRate.Proofs.cover7_leaf0290_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0290_certificate
#check SmaleRate.Proofs.cover7_leaf0291_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0291_certificate
#check SmaleRate.Proofs.cover7_leaf0292_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0292_certificate
#check SmaleRate.Proofs.cover7_leaf0293_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0293_certificate
#check SmaleRate.Proofs.cover7_leaf0294_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0294_certificate
#check SmaleRate.Proofs.cover7_leaf0295_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0295_certificate
#check SmaleRate.Proofs.cover7_leaf0296_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0296_certificate
#check SmaleRate.Proofs.cover7_leaf0297_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0297_certificate
#check SmaleRate.Proofs.cover7_leaf0298_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0298_certificate
#check SmaleRate.Proofs.cover7_leaf0299_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0299_certificate
