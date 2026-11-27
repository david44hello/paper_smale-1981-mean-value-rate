/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0300; no trusted numerical premise.
theorem cover8_leaf0300_exp_radius : (39921270703454921/40000000000000000 : ℝ) ≤ Real.exp ((-16527/1048576 : ℝ)/8) ∧ Real.exp ((-16527/1048576 : ℝ)/8) ≤ (499015883793186513/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16527/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0300_exp_lower : (4600567757729721/5000000000000000 : ℝ) ≤ Real.exp ((-10657048443129/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657048443129/16000000000000 : ℝ)/8) ≤ (920113551545944201/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657048443129/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0300_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215730857/31250000000 : ℝ) ≤ 4*Real.exp (8263/65536 : ℝ)*Real.exp (-mu (radius 8 (16527/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (64215730857/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16527/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0300_exp_radius
  have hrNumeric : (984362185037/1000000000000 : ℝ) ≤ Real.exp (-16527/1048576 : ℝ) ∧ Real.exp (-16527/1048576 : ℝ) ≤ (492181092519/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984362185037/1000000000000 : ℝ) ≤ (radius 8 (16527/131072 : ℝ)) ∧ (radius 8 (16527/131072 : ℝ)) ≤ (492181092519/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16527/131072 : ℝ)) (984362185037/1000000000000 : ℝ) (492181092519/500000000000 : ℝ) (1409251459/8000000000 : ℝ) (176156432381/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16527/131072 : ℝ)) (984362185037/1000000000000 : ℝ) (492181092519/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16527/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984362185037/1000000000000 : ℝ) (492181092519/500000000000 : ℝ) (496090546259/500000000000 : ℝ) (992181092519/1000000000000 : ℝ) (992150283493/1000000000000 : ℝ) (198430056699/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16527/131072 : ℝ)) 1 (496090546259/500000000000 : ℝ) (992181092519/1000000000000 : ℝ) (992150283493/1000000000000 : ℝ) (198430056699/200000000000 : ℝ) (198433137601/200000000000 : ℝ) (992165688007/1000000000000 : ℝ) (198433137577/200000000000 : ℝ) (62010355493/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16527/131072 : ℝ)) 2 (198433137601/200000000000 : ℝ) (992165688007/1000000000000 : ℝ) (198433137577/200000000000 : ℝ) (62010355493/62500000000 : ℝ) (198433137589/200000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16527/131072 : ℝ)) 3 (198433137589/200000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16527/131072 : ℝ)) 4 (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16527/131072 : ℝ)) 5 (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16527/131072 : ℝ)) 6 (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16527/131072 : ℝ)) 7 (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16527/131072 : ℝ))) (1409251459/8000000000 : ℝ) (176156432381/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16527/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1409251459/8000000000 : ℝ) (176156432381/1000000000000 : ℝ) (588078216187/1000000000000 : ℝ) (588078216191/1000000000000 : ℝ) (20985496919/50000000000 : ℝ) (104927484597/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16527/131072 : ℝ))) 1 (588078216187/1000000000000 : ℝ) (588078216191/1000000000000 : ℝ) (20985496919/50000000000 : ℝ) (104927484597/250000000000 : ℝ) (503894077283/1000000000000 : ℝ) (50389407729/100000000000 : ℝ) (49681210923/100000000000 : ℝ) (248406054619/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16527/131072 : ℝ))) 2 (503894077283/1000000000000 : ℝ) (50389407729/100000000000 : ℝ) (49681210923/100000000000 : ℝ) (248406054619/500000000000 : ℝ) (62544136657/125000000000 : ℝ) (31272068329/62500000000 : ℝ) (25017028169/50000000000 : ℝ) (125085140847/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16527/131072 : ℝ))) 3 (62544136657/125000000000 : ℝ) (31272068329/62500000000 : ℝ) (25017028169/50000000000 : ℝ) (125085140847/250000000000 : ℝ) (250173414159/500000000000 : ℝ) (250173414163/500000000000 : ℝ) (250173414139/500000000000 : ℝ) (500346828287/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16527/131072 : ℝ))) 4 (250173414159/500000000000 : ℝ) (250173414163/500000000000 : ℝ) (250173414139/500000000000 : ℝ) (500346828287/1000000000000 : ℝ) (250173414149/500000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16527/131072 : ℝ))) 5 (250173414149/500000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16527/131072 : ℝ))) 6 (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16527/131072 : ℝ))) 7 (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16527/131072 : ℝ)) hmem 8 (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16527/131072 : ℝ))) hcmem 8 (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16527/131072 : ℝ)) (124020710993/125000000000 : ℝ) (248041421987/250000000000 : ℝ) (500346828297/1000000000000 : ℝ) (500346828307/1000000000000 : ℝ) (792148901699/1000000000000 : ℝ) (792148901719/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0300_exp_lower
  have heNumeric : (64215730857/31250000000 : ℝ)/4 ≤ Real.exp (-10657048443129/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215730857/31250000000 : ℝ)/4 ≤ Real.exp ((8263/65536 : ℝ)-(792148901719/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8263/65536 : ℝ) (16527/131072 : ℝ) (792148901719/1000000000000 : ℝ) (64215730857/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0301; no trusted numerical premise.
theorem cover8_leaf0301_exp_radius : (499015824305861077/500000000000000000 : ℝ) ≤ Real.exp ((-1033/65536 : ℝ)/8) ∧ Real.exp ((-1033/65536 : ℝ)/8) ≤ (199606329722344431/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1033/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0301_exp_lower : (359419353182747/390625000000000 : ℝ) ≤ Real.exp ((-21314098944609/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314098944609/32000000000000 : ℝ)/8) ≤ (920113544147832321/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314098944609/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0301_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451627623/500000000000 : ℝ) ≤ 4*Real.exp (16527/131072 : ℝ)*Real.exp (-mu (radius 8 (1033/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451627623/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1033/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0301_exp_radius
  have hrNumeric : (984361246277/1000000000000 : ℝ) ≤ Real.exp (-1033/65536 : ℝ) ∧ Real.exp (-1033/65536 : ℝ) ≤ (492180623139/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984361246277/1000000000000 : ℝ) ≤ (radius 8 (1033/8192 : ℝ)) ∧ (radius 8 (1033/8192 : ℝ)) ≤ (492180623139/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1033/8192 : ℝ)) (984361246277/1000000000000 : ℝ) (492180623139/500000000000 : ℝ) (35232335617/200000000000 : ℝ) (44040419523/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1033/8192 : ℝ)) (984361246277/1000000000000 : ℝ) (492180623139/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1033/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984361246277/1000000000000 : ℝ) (492180623139/500000000000 : ℝ) (496090311569/500000000000 : ℝ) (992180623139/1000000000000 : ℝ) (1240187263/1250000000 : ℝ) (992149810401/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1033/8192 : ℝ)) 1 (496090311569/500000000000 : ℝ) (992180623139/1000000000000 : ℝ) (1240187263/1250000000 : ℝ) (992149810401/1000000000000 : ℝ) (992165216769/1000000000000 : ℝ) (99216521677/100000000000 : ℝ) (992165216649/1000000000000 : ℝ) (992165216651/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1033/8192 : ℝ)) 2 (992165216769/1000000000000 : ℝ) (99216521677/100000000000 : ℝ) (992165216649/1000000000000 : ℝ) (992165216651/1000000000000 : ℝ) (992165216709/1000000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1033/8192 : ℝ)) 3 (992165216709/1000000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1033/8192 : ℝ)) 4 (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1033/8192 : ℝ)) 5 (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1033/8192 : ℝ)) 6 (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1033/8192 : ℝ)) 7 (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1033/8192 : ℝ))) (35232335617/200000000000 : ℝ) (44040419523/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1033/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35232335617/200000000000 : ℝ) (44040419523/250000000000 : ℝ) (294040419521/500000000000 : ℝ) (294040419523/500000000000 : ℝ) (209858093771/500000000000 : ℝ) (419716187551/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1033/8192 : ℝ))) 1 (294040419521/500000000000 : ℝ) (294040419523/500000000000 : ℝ) (209858093771/500000000000 : ℝ) (419716187551/1000000000000 : ℝ) (125974628323/250000000000 : ℝ) (503898513299/1000000000000 : ℝ) (496816915703/1000000000000 : ℝ) (496816915711/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1033/8192 : ℝ))) 2 (125974628323/250000000000 : ℝ) (503898513299/1000000000000 : ℝ) (496816915703/1000000000000 : ℝ) (496816915711/1000000000000 : ℝ) (500357714497/1000000000000 : ℝ) (100071542901/200000000000 : ℝ) (500345186047/1000000000000 : ℝ) (62543148257/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1033/8192 : ℝ))) 3 (500357714497/1000000000000 : ℝ) (100071542901/200000000000 : ℝ) (500345186047/1000000000000 : ℝ) (62543148257/125000000000 : ℝ) (15635982821/31250000000 : ℝ) (500351450281/1000000000000 : ℝ) (62543931279/125000000000 : ℝ) (250175725121/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1033/8192 : ℝ))) 4 (15635982821/31250000000 : ℝ) (500351450281/1000000000000 : ℝ) (62543931279/125000000000 : ℝ) (250175725121/500000000000 : ℝ) (125087862563/250000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1033/8192 : ℝ))) 5 (125087862563/250000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1033/8192 : ℝ))) 6 (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1033/8192 : ℝ))) 7 (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1033/8192 : ℝ)) hmem 8 (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1033/8192 : ℝ))) hcmem 8 (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1033/8192 : ℝ)) (248041304177/250000000000 : ℝ) (992165216711/1000000000000 : ℝ) (500351450251/1000000000000 : ℝ) (250175725131/500000000000 : ℝ) (99019574427/125000000000 : ℝ) (792156595437/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0301_exp_lower
  have heNumeric : (1027451627623/500000000000 : ℝ)/4 ≤ Real.exp (-21314098944609/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451627623/500000000000 : ℝ)/4 ≤ Real.exp ((16527/131072 : ℝ)-(792156595437/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16527/131072 : ℝ) (1033/8192 : ℝ) (792156595437/1000000000000 : ℝ) (1027451627623/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0302; no trusted numerical premise.
theorem cover8_leaf0302_exp_radius : (199606305927417093/200000000000000000 : ℝ) ≤ Real.exp ((-16529/1048576 : ℝ)/8) ∧ Real.exp ((-16529/1048576 : ℝ)/8) ≤ (499015764818542733/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16529/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0302_exp_lower : (230028384196314971/250000000000000000 : ℝ) ≤ Real.exp ((-1332131312067/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332131312067/2000000000000 : ℝ)/8) ≤ (184022707357051977/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332131312067/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0302_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451561851/500000000000 : ℝ) ≤ 4*Real.exp (1033/8192 : ℝ)*Real.exp (-mu (radius 8 (16529/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451561851/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16529/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0302_exp_radius
  have hrNumeric : (984360307517/1000000000000 : ℝ) ≤ Real.exp (-16529/1048576 : ℝ) ∧ Real.exp (-16529/1048576 : ℝ) ≤ (492180153759/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984360307517/1000000000000 : ℝ) ≤ (radius 8 (16529/131072 : ℝ)) ∧ (radius 8 (16529/131072 : ℝ)) ≤ (492180153759/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16529/131072 : ℝ)) (984360307517/1000000000000 : ℝ) (492180153759/500000000000 : ℝ) (35233384727/200000000000 : ℝ) (176166923641/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16529/131072 : ℝ)) (984360307517/1000000000000 : ℝ) (492180153759/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16529/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984360307517/1000000000000 : ℝ) (492180153759/500000000000 : ℝ) (496090076879/500000000000 : ℝ) (992180153759/1000000000000 : ℝ) (496074668653/500000000000 : ℝ) (992149337307/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16529/131072 : ℝ)) 1 (496090076879/500000000000 : ℝ) (992180153759/1000000000000 : ℝ) (496074668653/500000000000 : ℝ) (992149337307/1000000000000 : ℝ) (248041186383/250000000000 : ℝ) (992164745533/1000000000000 : ℝ) (248041186353/250000000000 : ℝ) (496082372707/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16529/131072 : ℝ)) 2 (248041186383/250000000000 : ℝ) (992164745533/1000000000000 : ℝ) (248041186353/250000000000 : ℝ) (496082372707/500000000000 : ℝ) (3875643537/3906250000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16529/131072 : ℝ)) 3 (3875643537/3906250000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16529/131072 : ℝ)) 4 (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16529/131072 : ℝ)) 5 (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16529/131072 : ℝ)) 6 (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16529/131072 : ℝ)) 7 (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16529/131072 : ℝ))) (35233384727/200000000000 : ℝ) (176166923641/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16529/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35233384727/200000000000 : ℝ) (176166923641/1000000000000 : ℝ) (588083461817/1000000000000 : ℝ) (588083461821/1000000000000 : ℝ) (20986121821/50000000000 : ℝ) (104930609107/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16529/131072 : ℝ))) 1 (588083461817/1000000000000 : ℝ) (588083461821/1000000000000 : ℝ) (20986121821/50000000000 : ℝ) (104930609107/250000000000 : ℝ) (251951474559/500000000000 : ℝ) (4031223593/8000000000 : ℝ) (12420543049/25000000000 : ℝ) (31051357623/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16529/131072 : ℝ))) 2 (251951474559/500000000000 : ℝ) (4031223593/8000000000 : ℝ) (12420543049/25000000000 : ℝ) (31051357623/62500000000 : ℝ) (500362335539/1000000000000 : ℝ) (500362335547/1000000000000 : ℝ) (100069961703/200000000000 : ℝ) (125087452131/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16529/131072 : ℝ))) 3 (500362335539/1000000000000 : ℝ) (500362335547/1000000000000 : ℝ) (100069961703/200000000000 : ℝ) (125087452131/250000000000 : ℝ) (500356072027/1000000000000 : ℝ) (125089018009/250000000000 : ℝ) (500356071987/1000000000000 : ℝ) (500356071997/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16529/131072 : ℝ))) 4 (500356072027/1000000000000 : ℝ) (125089018009/250000000000 : ℝ) (500356071987/1000000000000 : ℝ) (500356071997/1000000000000 : ℝ) (500356072007/1000000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16529/131072 : ℝ))) 5 (500356072007/1000000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16529/131072 : ℝ))) 6 (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16529/131072 : ℝ))) 7 (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16529/131072 : ℝ)) hmem 8 (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16529/131072 : ℝ))) hcmem 8 (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16529/131072 : ℝ)) (992164745471/1000000000000 : ℝ) (496082372737/500000000000 : ℝ) (250178036003/500000000000 : ℝ) (500356072017/1000000000000 : ℝ) (31686571553/40000000000 : ℝ) (396082144423/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0302_exp_lower
  have heNumeric : (1027451561851/500000000000 : ℝ)/4 ≤ Real.exp (-1332131312067/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451561851/500000000000 : ℝ)/4 ≤ Real.exp ((1033/8192 : ℝ)-(396082144423/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1033/8192 : ℝ) (16529/131072 : ℝ) (396082144423/500000000000 : ℝ) (1027451561851/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0303; no trusted numerical premise.
theorem cover8_leaf0303_exp_radius : (998031410662462959/1000000000000000000 : ℝ) ≤ Real.exp ((-8265/524288 : ℝ)/8) ∧ Real.exp ((-8265/524288 : ℝ)/8) ≤ (12475392633280787/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8265/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0303_exp_lower : (920113529459147007/1000000000000000000 : ℝ) ≤ Real.exp ((-21314103031391/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314103031391/32000000000000 : ℝ)/8) ≤ (3594193474449793/3906250000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314103031391/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0303_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490299281/100000000000 : ℝ) ≤ 4*Real.exp (16529/131072 : ℝ)*Real.exp (-mu (radius 8 (8265/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (205490299281/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8265/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0303_exp_radius
  have hrNumeric : (492179684379/500000000000 : ℝ) ≤ Real.exp (-8265/524288 : ℝ) ∧ Real.exp (-8265/524288 : ℝ) ≤ (984359368759/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492179684379/500000000000 : ℝ) ≤ (radius 8 (8265/65536 : ℝ)) ∧ (radius 8 (8265/65536 : ℝ)) ≤ (984359368759/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8265/65536 : ℝ)) (492179684379/500000000000 : ℝ) (984359368759/1000000000000 : ℝ) (176172169017/1000000000000 : ℝ) (2752690141/15625000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8265/65536 : ℝ)) (492179684379/500000000000 : ℝ) (984359368759/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8265/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492179684379/500000000000 : ℝ) (984359368759/1000000000000 : ℝ) (992179684379/1000000000000 : ℝ) (49608984219/50000000000 : ℝ) (248037216053/250000000000 : ℝ) (992148864213/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8265/65536 : ℝ)) 1 (992179684379/1000000000000 : ℝ) (49608984219/50000000000 : ℝ) (248037216053/250000000000 : ℝ) (992148864213/1000000000000 : ℝ) (198432854859/200000000000 : ℝ) (992164274297/1000000000000 : ℝ) (39686570967/40000000000 : ℝ) (992164274177/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8265/65536 : ℝ)) 2 (198432854859/200000000000 : ℝ) (992164274297/1000000000000 : ℝ) (39686570967/40000000000 : ℝ) (992164274177/1000000000000 : ℝ) (198432854847/200000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8265/65536 : ℝ)) 3 (198432854847/200000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8265/65536 : ℝ)) 4 (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8265/65536 : ℝ)) 5 (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8265/65536 : ℝ)) 6 (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8265/65536 : ℝ)) 7 (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8265/65536 : ℝ))) (176172169017/1000000000000 : ℝ) (2752690141/15625000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8265/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176172169017/1000000000000 : ℝ) (2752690141/15625000000 : ℝ) (147021521127/250000000000 : ℝ) (18377690141/31250000000 : ℝ) (209864342503/500000000000 : ℝ) (83945737003/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8265/65536 : ℝ))) 1 (147021521127/250000000000 : ℝ) (18377690141/31250000000 : ℝ) (209864342503/500000000000 : ℝ) (83945737003/200000000000 : ℝ) (503907384757/1000000000000 : ℝ) (125976846191/250000000000 : ℝ) (124206631999/250000000000 : ℝ) (124206632001/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8265/65536 : ℝ))) 2 (503907384757/1000000000000 : ℝ) (125976846191/250000000000 : ℝ) (124206631999/250000000000 : ℝ) (124206632001/250000000000 : ℝ) (62545869547/125000000000 : ℝ) (15636467387/31250000000 : ℝ) (500354430779/1000000000000 : ℝ) (500354430787/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8265/65536 : ℝ))) 3 (62545869547/125000000000 : ℝ) (15636467387/31250000000 : ℝ) (500354430779/1000000000000 : ℝ) (500354430787/1000000000000 : ℝ) (500360693577/1000000000000 : ℝ) (250180346793/500000000000 : ℝ) (250180346769/500000000000 : ℝ) (500360693547/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8265/65536 : ℝ))) 4 (500360693577/1000000000000 : ℝ) (250180346793/500000000000 : ℝ) (250180346769/500000000000 : ℝ) (500360693547/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8265/65536 : ℝ))) 5 (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8265/65536 : ℝ))) 6 (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8265/65536 : ℝ))) 7 (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8265/65536 : ℝ)) hmem 8 (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8265/65536 : ℝ))) hcmem 8 (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8265/65536 : ℝ)) (496082137117/500000000000 : ℝ) (992164274237/1000000000000 : ℝ) (500360693557/1000000000000 : ℝ) (500360693567/1000000000000 : ℝ) (792171981919/1000000000000 : ℝ) (396085990969/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0303_exp_lower
  have heNumeric : (205490299281/100000000000 : ℝ)/4 ≤ Real.exp (-21314103031391/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490299281/100000000000 : ℝ)/4 ≤ Real.exp ((16529/131072 : ℝ)-(396085990969/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16529/131072 : ℝ) (8265/65536 : ℝ) (396085990969/500000000000 : ℝ) (205490299281/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0304; no trusted numerical premise.
theorem cover8_leaf0304_exp_radius : (249507822921963659/250000000000000000 : ℝ) ≤ Real.exp ((-16531/1048576 : ℝ)/8) ∧ Real.exp ((-16531/1048576 : ℝ)/8) ≤ (998031291687854637/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16531/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0304_exp_lower : (184022704434059757/200000000000000000 : ℝ) ≤ Real.exp ((-10657052529671/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657052529671/16000000000000 : ℝ)/8) ≤ (460056761085149393/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657052529671/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0304_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862857823/125000000000 : ℝ) ≤ 4*Real.exp (8265/65536 : ℝ)*Real.exp (-mu (radius 8 (16531/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862857823/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16531/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0304_exp_radius
  have hrNumeric : (984358430001/1000000000000 : ℝ) ≤ Real.exp (-16531/1048576 : ℝ) ∧ Real.exp (-16531/1048576 : ℝ) ≤ (492179215001/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984358430001/1000000000000 : ℝ) ≤ (radius 8 (16531/131072 : ℝ)) ∧ (radius 8 (16531/131072 : ℝ)) ≤ (492179215001/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16531/131072 : ℝ)) (984358430001/1000000000000 : ℝ) (492179215001/500000000000 : ℝ) (176177414227/1000000000000 : ℝ) (88088707117/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16531/131072 : ℝ)) (984358430001/1000000000000 : ℝ) (492179215001/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16531/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984358430001/1000000000000 : ℝ) (492179215001/500000000000 : ℝ) (198435843/200000000 : ℝ) (992179215001/1000000000000 : ℝ) (992148391119/1000000000000 : ℝ) (12401854889/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16531/131072 : ℝ)) 1 (198435843/200000000 : ℝ) (992179215001/1000000000000 : ℝ) (992148391119/1000000000000 : ℝ) (12401854889/12500000000 : ℝ) (992163803059/1000000000000 : ℝ) (992163803061/1000000000000 : ℝ) (992163802939/1000000000000 : ℝ) (992163802941/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16531/131072 : ℝ)) 2 (992163803059/1000000000000 : ℝ) (992163803061/1000000000000 : ℝ) (992163802939/1000000000000 : ℝ) (992163802941/1000000000000 : ℝ) (992163802999/1000000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16531/131072 : ℝ)) 3 (992163802999/1000000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16531/131072 : ℝ)) 4 (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16531/131072 : ℝ)) 5 (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16531/131072 : ℝ)) 6 (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16531/131072 : ℝ)) 7 (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16531/131072 : ℝ))) (176177414227/1000000000000 : ℝ) (88088707117/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16531/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176177414227/1000000000000 : ℝ) (88088707117/500000000000 : ℝ) (588088707113/1000000000000 : ℝ) (588088707117/1000000000000 : ℝ) (419734933293/1000000000000 : ℝ) (209867466651/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16531/131072 : ℝ))) 1 (588088707113/1000000000000 : ℝ) (588088707117/1000000000000 : ℝ) (419734933293/1000000000000 : ℝ) (209867466651/500000000000 : ℝ) (503911820203/1000000000000 : ℝ) (50391182021/100000000000 : ℝ) (124207833451/250000000000 : ℝ) (496831333813/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16531/131072 : ℝ))) 2 (503911820203/1000000000000 : ℝ) (50391182021/100000000000 : ℝ) (124207833451/250000000000 : ℝ) (496831333813/1000000000000 : ℝ) (500371577003/1000000000000 : ℝ) (125092894253/250000000000 : ℝ) (15636220401/31250000000 : ℝ) (500359052841/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16531/131072 : ℝ))) 3 (500371577003/1000000000000 : ℝ) (125092894253/250000000000 : ℝ) (15636220401/31250000000 : ℝ) (500359052841/1000000000000 : ℝ) (500365314917/1000000000000 : ℝ) (500365314927/1000000000000 : ℝ) (250182657439/500000000000 : ℝ) (62545664361/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16531/131072 : ℝ))) 4 (500365314917/1000000000000 : ℝ) (500365314927/1000000000000 : ℝ) (250182657439/500000000000 : ℝ) (62545664361/125000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16531/131072 : ℝ))) 5 (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16531/131072 : ℝ))) 6 (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16531/131072 : ℝ))) 7 (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16531/131072 : ℝ)) hmem 8 (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16531/131072 : ℝ))) hcmem 8 (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16531/131072 : ℝ)) (496081901499/500000000000 : ℝ) (992163803001/1000000000000 : ℝ) (500365314897/1000000000000 : ℝ) (125091328727/250000000000 : ℝ) (158435934937/200000000000 : ℝ) (396089837353/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0304_exp_lower
  have heNumeric : (256862857823/125000000000 : ℝ)/4 ≤ Real.exp (-10657052529671/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862857823/125000000000 : ℝ)/4 ≤ Real.exp ((8265/65536 : ℝ)-(396089837353/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8265/65536 : ℝ) (16531/131072 : ℝ) (396089837353/500000000000 : ℝ) (256862857823/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0305; no trusted numerical premise.
theorem cover8_leaf0305_exp_radius : (62376948294578781/62500000000000000 : ℝ) ≤ Real.exp ((-4133/262144 : ℝ)/8) ∧ Real.exp ((-4133/262144 : ℝ)/8) ≤ (998031172713260497/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4133/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0305_exp_lower : (920113514917220033/1000000000000000000 : ℝ) ≤ Real.exp ((-21314107077341/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314107077341/32000000000000 : ℝ)/8) ≤ (460056757458610017/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314107077341/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0305_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725683249/250000000000 : ℝ) ≤ 4*Real.exp (16531/131072 : ℝ)*Real.exp (-mu (radius 8 (4133/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513725683249/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4133/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0305_exp_radius
  have hrNumeric : (246089372811/250000000000 : ℝ) ≤ Real.exp (-4133/262144 : ℝ) ∧ Real.exp (-4133/262144 : ℝ) ≤ (196871498249/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246089372811/250000000000 : ℝ) ≤ (radius 8 (4133/32768 : ℝ)) ∧ (radius 8 (4133/32768 : ℝ)) ≤ (196871498249/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4133/32768 : ℝ)) (246089372811/250000000000 : ℝ) (196871498249/200000000000 : ℝ) (44045664819/250000000000 : ℝ) (176182659283/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4133/32768 : ℝ)) (246089372811/250000000000 : ℝ) (196871498249/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4133/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246089372811/250000000000 : ℝ) (196871498249/200000000000 : ℝ) (496089372811/500000000000 : ℝ) (992178745623/1000000000000 : ℝ) (496073959013/500000000000 : ℝ) (992147918027/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4133/32768 : ℝ)) 1 (496089372811/500000000000 : ℝ) (992178745623/1000000000000 : ℝ) (496073959013/500000000000 : ℝ) (992147918027/1000000000000 : ℝ) (62010208239/62500000000 : ℝ) (39686533273/40000000000 : ℝ) (124020416463/125000000000 : ℝ) (496081665853/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4133/32768 : ℝ)) 2 (62010208239/62500000000 : ℝ) (39686533273/40000000000 : ℝ) (124020416463/125000000000 : ℝ) (496081665853/500000000000 : ℝ) (248040832941/250000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4133/32768 : ℝ)) 3 (248040832941/250000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4133/32768 : ℝ)) 4 (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4133/32768 : ℝ)) 5 (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4133/32768 : ℝ)) 6 (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4133/32768 : ℝ)) 7 (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4133/32768 : ℝ))) (44045664819/250000000000 : ℝ) (176182659283/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4133/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44045664819/250000000000 : ℝ) (176182659283/1000000000000 : ℝ) (294045664819/500000000000 : ℝ) (294045664821/500000000000 : ℝ) (26233823831/62500000000 : ℝ) (83948236261/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4133/32768 : ℝ))) 1 (294045664819/500000000000 : ℝ) (294045664821/500000000000 : ℝ) (26233823831/62500000000 : ℝ) (83948236261/200000000000 : ℝ) (503916255467/1000000000000 : ℝ) (251958127737/500000000000 : ℝ) (248418069699/500000000000 : ℝ) (248418069703/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4133/32768 : ℝ))) 2 (503916255467/1000000000000 : ℝ) (251958127737/500000000000 : ℝ) (248418069699/500000000000 : ℝ) (248418069703/500000000000 : ℝ) (62547024679/125000000000 : ℝ) (1563675617/3125000000 : ℝ) (250181837343/500000000000 : ℝ) (100072734939/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4133/32768 : ℝ))) 3 (62547024679/125000000000 : ℝ) (1563675617/3125000000 : ℝ) (250181837343/500000000000 : ℝ) (100072734939/200000000000 : ℝ) (500369936059/1000000000000 : ℝ) (125092484017/250000000000 : ℝ) (500369936019/1000000000000 : ℝ) (500369936029/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4133/32768 : ℝ))) 4 (500369936059/1000000000000 : ℝ) (125092484017/250000000000 : ℝ) (500369936019/1000000000000 : ℝ) (500369936029/1000000000000 : ℝ) (500369936039/1000000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4133/32768 : ℝ))) 5 (500369936039/1000000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4133/32768 : ℝ))) 6 (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4133/32768 : ℝ))) 7 (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4133/32768 : ℝ)) hmem 8 (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4133/32768 : ℝ))) hcmem 8 (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4133/32768 : ℝ)) (992163331763/1000000000000 : ℝ) (496081665883/500000000000 : ℝ) (250184968019/500000000000 : ℝ) (500369936049/1000000000000 : ℝ) (396093683571/500000000000 : ℝ) (792187367163/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0305_exp_lower
  have heNumeric : (513725683249/250000000000 : ℝ)/4 ≤ Real.exp (-21314107077341/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725683249/250000000000 : ℝ)/4 ≤ Real.exp ((16531/131072 : ℝ)-(792187367163/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16531/131072 : ℝ) (4133/32768 : ℝ) (792187367163/1000000000000 : ℝ) (513725683249/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0306; no trusted numerical premise.
theorem cover8_leaf0306_exp_radius : (998031053738680539/1000000000000000000 : ℝ) ≤ Real.exp ((-16533/1048576 : ℝ)/8) ∧ Real.exp ((-16533/1048576 : ℝ)/8) ≤ (49901552686934027/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16533/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0306_exp_lower : (920113507700485823/1000000000000000000 : ℝ) ≤ Real.exp ((-5328527271307/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328527271307/8000000000000 : ℝ)/8) ≤ (14376773557820091/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328527271307/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0306_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451302029/500000000000 : ℝ) ≤ 4*Real.exp (4133/32768 : ℝ)*Real.exp (-mu (radius 8 (16533/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451302029/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16533/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0306_exp_radius
  have hrNumeric : (123044569061/125000000000 : ℝ) ≤ Real.exp (-16533/1048576 : ℝ) ∧ Real.exp (-16533/1048576 : ℝ) ≤ (984356552489/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123044569061/125000000000 : ℝ) ≤ (radius 8 (16533/131072 : ℝ)) ∧ (radius 8 (16533/131072 : ℝ)) ≤ (984356552489/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16533/131072 : ℝ)) (123044569061/125000000000 : ℝ) (984356552489/1000000000000 : ℝ) (176187904159/1000000000000 : ℝ) (35237580833/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16533/131072 : ℝ)) (123044569061/125000000000 : ℝ) (984356552489/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16533/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123044569061/125000000000 : ℝ) (984356552489/1000000000000 : ℝ) (248044569061/250000000000 : ℝ) (198435655249/200000000000 : ℝ) (992147444933/1000000000000 : ℝ) (496073722467/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16533/131072 : ℝ)) 1 (248044569061/250000000000 : ℝ) (198435655249/200000000000 : ℝ) (992147444933/1000000000000 : ℝ) (496073722467/500000000000 : ℝ) (248040715147/250000000000 : ℝ) (99216286059/100000000000 : ℝ) (248040715117/250000000000 : ℝ) (99216286047/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16533/131072 : ℝ)) 2 (248040715147/250000000000 : ℝ) (99216286059/100000000000 : ℝ) (248040715117/250000000000 : ℝ) (99216286047/100000000000 : ℝ) (62010178783/62500000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16533/131072 : ℝ)) 3 (62010178783/62500000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16533/131072 : ℝ)) 4 (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16533/131072 : ℝ)) 5 (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16533/131072 : ℝ)) 6 (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16533/131072 : ℝ)) 7 (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16533/131072 : ℝ))) (176187904159/1000000000000 : ℝ) (35237580833/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16533/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176187904159/1000000000000 : ℝ) (35237580833/200000000000 : ℝ) (588093952079/1000000000000 : ℝ) (588093952083/1000000000000 : ℝ) (26234214313/62500000000 : ℝ) (52468428627/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16533/131072 : ℝ))) 1 (588093952079/1000000000000 : ℝ) (588093952083/1000000000000 : ℝ) (26234214313/62500000000 : ℝ) (52468428627/125000000000 : ℝ) (503920690543/1000000000000 : ℝ) (10078413811/20000000000 : ℝ) (49684094477/100000000000 : ℝ) (496840944777/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16533/131072 : ℝ))) 2 (503920690543/1000000000000 : ℝ) (10078413811/20000000000 : ℝ) (49684094477/100000000000 : ℝ) (496840944777/1000000000000 : ℝ) (62547602207/125000000000 : ℝ) (1954612569/3906250000 : ℝ) (31273018521/62500000000 : ℝ) (62546037043/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16533/131072 : ℝ))) 3 (62547602207/125000000000 : ℝ) (1954612569/3906250000 : ℝ) (31273018521/62500000000 : ℝ) (62546037043/125000000000 : ℝ) (125093639249/250000000000 : ℝ) (125093639251/250000000000 : ℝ) (125093639239/250000000000 : ℝ) (100074911393/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16533/131072 : ℝ))) 4 (125093639249/250000000000 : ℝ) (125093639251/250000000000 : ℝ) (125093639239/250000000000 : ℝ) (100074911393/200000000000 : ℝ) (31273409811/62500000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16533/131072 : ℝ))) 5 (31273409811/62500000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16533/131072 : ℝ))) 6 (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16533/131072 : ℝ))) 7 (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16533/131072 : ℝ)) hmem 8 (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16533/131072 : ℝ))) hcmem 8 (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16533/131072 : ℝ)) (992162860527/1000000000000 : ℝ) (99216286053/100000000000 : ℝ) (20014982279/40000000000 : ℝ) (100074911397/200000000000 : ℝ) (158439011857/200000000000 : ℝ) (99024382413/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0306_exp_lower
  have heNumeric : (1027451302029/500000000000 : ℝ)/4 ≤ Real.exp (-5328527271307/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451302029/500000000000 : ℝ)/4 ≤ Real.exp ((4133/32768 : ℝ)-(99024382413/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4133/32768 : ℝ) (16533/131072 : ℝ) (99024382413/125000000000 : ℝ) (1027451302029/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0307; no trusted numerical premise.
theorem cover8_leaf0307_exp_radius : (249507733691028691/250000000000000000 : ℝ) ≤ Real.exp ((-8267/524288 : ℝ)/8) ∧ Real.exp ((-8267/524288 : ℝ)/8) ≤ (199606186952822953/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8267/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0307_exp_lower : (460056750259990569/500000000000000000 : ℝ) ≤ Real.exp ((-4262822216607/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262822216607/6400000000000 : ℝ)/8) ≤ (920113500519981139/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262822216607/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0307_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862809471/125000000000 : ℝ) ≤ 4*Real.exp (16533/131072 : ℝ)*Real.exp (-mu (radius 8 (8267/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (256862809471/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8267/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0307_exp_radius
  have hrNumeric : (984355613733/1000000000000 : ℝ) ≤ Real.exp (-8267/524288 : ℝ) ∧ Real.exp (-8267/524288 : ℝ) ≤ (492177806867/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984355613733/1000000000000 : ℝ) ≤ (radius 8 (8267/65536 : ℝ)) ∧ (radius 8 (8267/65536 : ℝ)) ≤ (492177806867/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8267/65536 : ℝ)) (984355613733/1000000000000 : ℝ) (492177806867/500000000000 : ℝ) (88096574437/500000000000 : ℝ) (176193148881/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8267/65536 : ℝ)) (984355613733/1000000000000 : ℝ) (492177806867/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8267/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984355613733/1000000000000 : ℝ) (492177806867/500000000000 : ℝ) (496088903433/500000000000 : ℝ) (992177806867/1000000000000 : ℝ) (3100459287/3125000000 : ℝ) (496073485921/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8267/65536 : ℝ)) 1 (496088903433/500000000000 : ℝ) (992177806867/1000000000000 : ℝ) (3100459287/3125000000 : ℝ) (496073485921/500000000000 : ℝ) (992162389353/1000000000000 : ℝ) (198432477871/200000000000 : ℝ) (992162389233/1000000000000 : ℝ) (198432477847/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8267/65536 : ℝ)) 2 (992162389353/1000000000000 : ℝ) (198432477871/200000000000 : ℝ) (992162389233/1000000000000 : ℝ) (198432477847/200000000000 : ℝ) (992162389293/1000000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8267/65536 : ℝ)) 3 (992162389293/1000000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8267/65536 : ℝ)) 4 (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8267/65536 : ℝ)) 5 (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8267/65536 : ℝ)) 6 (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8267/65536 : ℝ)) 7 (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8267/65536 : ℝ))) (88096574437/500000000000 : ℝ) (176193148881/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8267/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88096574437/500000000000 : ℝ) (176193148881/1000000000000 : ℝ) (588096574437/1000000000000 : ℝ) (588096574441/1000000000000 : ℝ) (419753676427/1000000000000 : ℝ) (104938419109/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8267/65536 : ℝ))) 1 (588096574437/1000000000000 : ℝ) (588096574441/1000000000000 : ℝ) (419753676427/1000000000000 : ℝ) (104938419109/250000000000 : ℝ) (62990640679/125000000000 : ℝ) (503925125439/1000000000000 : ℝ) (3105285937/6250000000 : ℝ) (62105718741/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8267/65536 : ℝ))) 2 (62990640679/125000000000 : ℝ) (503925125439/1000000000000 : ℝ) (3105285937/6250000000 : ℝ) (62105718741/125000000000 : ℝ) (125096359419/250000000000 : ℝ) (125096359421/250000000000 : ℝ) (500372917781/1000000000000 : ℝ) (500372917789/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8267/65536 : ℝ))) 3 (125096359419/250000000000 : ℝ) (125096359421/250000000000 : ℝ) (500372917781/1000000000000 : ℝ) (500372917789/1000000000000 : ℝ) (1954606163/3906250000 : ℝ) (500379177737/1000000000000 : ℝ) (500379177689/1000000000000 : ℝ) (250189588849/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8267/65536 : ℝ))) 4 (1954606163/3906250000 : ℝ) (500379177737/1000000000000 : ℝ) (500379177689/1000000000000 : ℝ) (250189588849/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8267/65536 : ℝ))) 5 (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8267/65536 : ℝ))) 6 (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8267/65536 : ℝ))) 7 (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8267/65536 : ℝ)) hmem 8 (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8267/65536 : ℝ))) hcmem 8 (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8267/65536 : ℝ)) (248040597323/250000000000 : ℝ) (198432477859/200000000000 : ℝ) (125094794427/250000000000 : ℝ) (250189588859/500000000000 : ℝ) (792202751111/1000000000000 : ℝ) (79220275113/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0307_exp_lower
  have heNumeric : (256862809471/125000000000 : ℝ)/4 ≤ Real.exp (-4262822216607/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862809471/125000000000 : ℝ)/4 ≤ Real.exp ((16533/131072 : ℝ)-(79220275113/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16533/131072 : ℝ) (8267/65536 : ℝ) (79220275113/100000000000 : ℝ) (256862809471/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0308; no trusted numerical premise.
theorem cover8_leaf0308_exp_radius : (998030815789563173/1000000000000000000 : ℝ) ≤ Real.exp ((-16535/1048576 : ℝ)/8) ∧ Real.exp ((-16535/1048576 : ℝ)/8) ≤ (499015407894781587/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16535/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0308_exp_lower : (460056746687622961/500000000000000000 : ℝ) ≤ Real.exp ((-2131411307089/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131411307089/3200000000000 : ℝ)/8) ≤ (920113493375245923/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131411307089/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0308_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725587029/250000000000 : ℝ) ≤ 4*Real.exp (8267/65536 : ℝ)*Real.exp (-mu (radius 8 (16535/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725587029/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16535/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0308_exp_radius
  have hrNumeric : (492177337489/500000000000 : ℝ) ≤ Real.exp (-16535/1048576 : ℝ) ∧ Real.exp (-16535/1048576 : ℝ) ≤ (984354674979/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492177337489/500000000000 : ℝ) ≤ (radius 8 (16535/131072 : ℝ)) ∧ (radius 8 (16535/131072 : ℝ)) ≤ (984354674979/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16535/131072 : ℝ)) (492177337489/500000000000 : ℝ) (984354674979/1000000000000 : ℝ) (176198393429/1000000000000 : ℝ) (35239678687/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16535/131072 : ℝ)) (492177337489/500000000000 : ℝ) (984354674979/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16535/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492177337489/500000000000 : ℝ) (984354674979/1000000000000 : ℝ) (992177337489/1000000000000 : ℝ) (99217733749/100000000000 : ℝ) (248036624687/250000000000 : ℝ) (992146498749/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16535/131072 : ℝ)) 1 (992177337489/1000000000000 : ℝ) (99217733749/100000000000 : ℝ) (248036624687/250000000000 : ℝ) (992146498749/1000000000000 : ℝ) (496080959059/500000000000 : ℝ) (24804047953/25000000000 : ℝ) (496080958999/500000000000 : ℝ) (496080959/500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16535/131072 : ℝ)) 2 (496080959059/500000000000 : ℝ) (24804047953/25000000000 : ℝ) (496080958999/500000000000 : ℝ) (496080959/500000000 : ℝ) (496080959029/500000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16535/131072 : ℝ)) 3 (496080959029/500000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16535/131072 : ℝ)) 4 (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16535/131072 : ℝ)) 5 (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16535/131072 : ℝ)) 6 (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16535/131072 : ℝ)) 7 (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16535/131072 : ℝ))) (176198393429/1000000000000 : ℝ) (35239678687/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16535/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176198393429/1000000000000 : ℝ) (35239678687/200000000000 : ℝ) (294049598357/500000000000 : ℝ) (294049598359/500000000000 : ℝ) (209879961781/500000000000 : ℝ) (41975992357/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16535/131072 : ℝ))) 1 (294049598357/500000000000 : ℝ) (294049598359/500000000000 : ℝ) (209879961781/500000000000 : ℝ) (41975992357/100000000000 : ℝ) (251964780069/500000000000 : ℝ) (31495597509/62500000000 : ℝ) (248425277427/500000000000 : ℝ) (248425277431/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16535/131072 : ℝ))) 2 (251964780069/500000000000 : ℝ) (31495597509/62500000000 : ℝ) (248425277427/500000000000 : ℝ) (248425277431/500000000000 : ℝ) (62548757187/125000000000 : ℝ) (500390057503/1000000000000 : ℝ) (250188769513/500000000000 : ℝ) (250188769517/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16535/131072 : ℝ))) 3 (62548757187/125000000000 : ℝ) (500390057503/1000000000000 : ℝ) (250188769513/500000000000 : ℝ) (250188769517/500000000000 : ℝ) (500383798261/1000000000000 : ℝ) (500383798269/1000000000000 : ℝ) (500383798221/1000000000000 : ℝ) (50038379823/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16535/131072 : ℝ))) 4 (500383798261/1000000000000 : ℝ) (500383798269/1000000000000 : ℝ) (500383798221/1000000000000 : ℝ) (50038379823/100000000000 : ℝ) (500383798241/1000000000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16535/131072 : ℝ))) 5 (500383798241/1000000000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16535/131072 : ℝ))) 6 (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16535/131072 : ℝ))) 7 (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16535/131072 : ℝ)) hmem 8 (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16535/131072 : ℝ))) hcmem 8 (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16535/131072 : ℝ)) (992161918057/1000000000000 : ℝ) (49608095903/50000000000 : ℝ) (3127398739/6250000000 : ℝ) (2001535193/4000000000 : ℝ) (396105221313/500000000000 : ℝ) (158442088529/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0308_exp_lower
  have heNumeric : (513725587029/250000000000 : ℝ)/4 ≤ Real.exp (-2131411307089/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725587029/250000000000 : ℝ)/4 ≤ Real.exp ((8267/65536 : ℝ)-(158442088529/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8267/65536 : ℝ) (16535/131072 : ℝ) (158442088529/200000000000 : ℝ) (513725587029/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0309; no trusted numerical premise.
theorem cover8_leaf0309_exp_radius : (249507674203756441/250000000000000000 : ℝ) ≤ Real.exp ((-2067/131072 : ℝ)/8) ∧ Real.exp ((-2067/131072 : ℝ)/8) ≤ (199606139363005153/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2067/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0309_exp_lower : (230028371566943839/250000000000000000 : ℝ) ≤ Real.exp ((-21314115048377/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314115048377/32000000000000 : ℝ)/8) ≤ (920113486267775357/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314115048377/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0309_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902221131/1000000000000 : ℝ) ≤ 4*Real.exp (16535/131072 : ℝ)*Real.exp (-mu (radius 8 (2067/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902221131/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2067/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0309_exp_radius
  have hrNumeric : (39374149449/40000000000 : ℝ) ≤ Real.exp (-2067/131072 : ℝ) ∧ Real.exp (-2067/131072 : ℝ) ≤ (492176868113/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39374149449/40000000000 : ℝ) ≤ (radius 8 (2067/16384 : ℝ)) ∧ (radius 8 (2067/16384 : ℝ)) ≤ (492176868113/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2067/16384 : ℝ)) (39374149449/40000000000 : ℝ) (492176868113/500000000000 : ℝ) (176203637811/1000000000000 : ℝ) (176203637817/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2067/16384 : ℝ)) (39374149449/40000000000 : ℝ) (492176868113/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2067/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39374149449/40000000000 : ℝ) (492176868113/500000000000 : ℝ) (62011054257/62500000000 : ℝ) (992176868113/1000000000000 : ℝ) (124018253207/125000000000 : ℝ) (992146025657/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2067/16384 : ℝ)) 1 (62011054257/62500000000 : ℝ) (992176868113/1000000000000 : ℝ) (124018253207/125000000000 : ℝ) (992146025657/1000000000000 : ℝ) (248040361721/250000000000 : ℝ) (198432289377/200000000000 : ℝ) (248040361691/250000000000 : ℝ) (496080723383/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2067/16384 : ℝ)) 2 (248040361721/250000000000 : ℝ) (198432289377/200000000000 : ℝ) (248040361691/250000000000 : ℝ) (496080723383/500000000000 : ℝ) (124020180853/125000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2067/16384 : ℝ)) 3 (124020180853/125000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2067/16384 : ℝ)) 4 (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2067/16384 : ℝ)) 5 (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2067/16384 : ℝ)) 6 (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2067/16384 : ℝ)) 7 (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2067/16384 : ℝ))) (176203637811/1000000000000 : ℝ) (176203637817/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2067/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176203637811/1000000000000 : ℝ) (176203637817/1000000000000 : ℝ) (117620363781/200000000000 : ℝ) (588101818909/1000000000000 : ℝ) (209883085199/500000000000 : ℝ) (209883085203/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2067/16384 : ℝ))) 1 (117620363781/200000000000 : ℝ) (588101818909/1000000000000 : ℝ) (209883085199/500000000000 : ℝ) (209883085203/500000000000 : ℝ) (503933994651/1000000000000 : ℝ) (251966997329/500000000000 : ℝ) (248427679781/500000000000 : ℝ) (496855359569/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2067/16384 : ℝ))) 2 (503933994651/1000000000000 : ℝ) (251966997329/500000000000 : ℝ) (248427679781/500000000000 : ℝ) (496855359569/1000000000000 : ℝ) (250197338553/500000000000 : ℝ) (250197338557/500000000000 : ℝ) (500382160061/1000000000000 : ℝ) (500382160069/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2067/16384 : ℝ))) 3 (250197338553/500000000000 : ℝ) (250197338557/500000000000 : ℝ) (500382160061/1000000000000 : ℝ) (500382160069/1000000000000 : ℝ) (500388418583/1000000000000 : ℝ) (15637138081/31250000000 : ℝ) (31274276159/62500000000 : ℝ) (500388418553/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2067/16384 : ℝ))) 4 (500388418583/1000000000000 : ℝ) (15637138081/31250000000 : ℝ) (31274276159/62500000000 : ℝ) (500388418553/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2067/16384 : ℝ))) 5 (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2067/16384 : ℝ))) 6 (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2067/16384 : ℝ))) 7 (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2067/16384 : ℝ)) hmem 8 (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2067/16384 : ℝ))) hcmem 8 (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2067/16384 : ℝ)) (992161446823/1000000000000 : ℝ) (496080723413/500000000000 : ℝ) (500388418563/1000000000000 : ℝ) (500388418573/1000000000000 : ℝ) (99027266727/125000000000 : ℝ) (198054533459/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0309_exp_lower
  have heNumeric : (2054902221131/1000000000000 : ℝ)/4 ≤ Real.exp (-21314115048377/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902221131/1000000000000 : ℝ)/4 ≤ Real.exp ((16535/131072 : ℝ)-(198054533459/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16535/131072 : ℝ) (2067/16384 : ℝ) (198054533459/250000000000 : ℝ) (2054902221131/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0310; no trusted numerical premise.
theorem cover8_leaf0310_exp_radius : (998030577840502539/1000000000000000000 : ℝ) ≤ Real.exp ((-16537/1048576 : ℝ)/8) ∧ Real.exp ((-16537/1048576 : ℝ)/8) ≤ (49901528892025127/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16537/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0310_exp_lower : (920113479196649329/1000000000000000000 : ℝ) ≤ Real.exp ((-2664264626969/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664264626969/4000000000000 : ℝ)/8) ≤ (92011347919664933/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664264626969/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0310_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451047397/500000000000 : ℝ) ≤ 4*Real.exp (2067/16384 : ℝ)*Real.exp (-mu (radius 8 (16537/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451047397/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16537/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0310_exp_radius
  have hrNumeric : (984352797473/1000000000000 : ℝ) ≤ Real.exp (-16537/1048576 : ℝ) ∧ Real.exp (-16537/1048576 : ℝ) ≤ (492176398737/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984352797473/1000000000000 : ℝ) ≤ (radius 8 (16537/131072 : ℝ)) ∧ (radius 8 (16537/131072 : ℝ)) ≤ (492176398737/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16537/131072 : ℝ)) (984352797473/1000000000000 : ℝ) (492176398737/500000000000 : ℝ) (88104441013/500000000000 : ℝ) (176208882033/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16537/131072 : ℝ)) (984352797473/1000000000000 : ℝ) (492176398737/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16537/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984352797473/1000000000000 : ℝ) (492176398737/500000000000 : ℝ) (62011024921/62500000000 : ℝ) (992176398737/1000000000000 : ℝ) (248036388141/250000000000 : ℝ) (198429110513/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16537/131072 : ℝ)) 1 (62011024921/62500000000 : ℝ) (992176398737/1000000000000 : ℝ) (248036388141/250000000000 : ℝ) (198429110513/200000000000 : ℝ) (19843219513/20000000000 : ℝ) (992160975651/1000000000000 : ℝ) (99216097553/100000000000 : ℝ) (248040243883/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16537/131072 : ℝ)) 2 (19843219513/20000000000 : ℝ) (992160975651/1000000000000 : ℝ) (99216097553/100000000000 : ℝ) (248040243883/250000000000 : ℝ) (99216097559/100000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16537/131072 : ℝ)) 3 (99216097559/100000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16537/131072 : ℝ)) 4 (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16537/131072 : ℝ)) 5 (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16537/131072 : ℝ)) 6 (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16537/131072 : ℝ)) 7 (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16537/131072 : ℝ))) (88104441013/500000000000 : ℝ) (176208882033/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16537/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88104441013/500000000000 : ℝ) (176208882033/1000000000000 : ℝ) (588104441013/1000000000000 : ℝ) (588104441017/1000000000000 : ℝ) (209886208471/500000000000 : ℝ) (52471552119/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16537/131072 : ℝ))) 1 (588104441013/1000000000000 : ℝ) (588104441017/1000000000000 : ℝ) (209886208471/500000000000 : ℝ) (52471552119/125000000000 : ℝ) (503938428977/1000000000000 : ℝ) (100787685797/200000000000 : ℝ) (31053760253/62500000000 : ℝ) (496860164057/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16537/131072 : ℝ))) 2 (503938428977/1000000000000 : ℝ) (100787685797/200000000000 : ℝ) (31053760253/62500000000 : ℝ) (496860164057/1000000000000 : ℝ) (122167797/244140625 : ℝ) (500399296521/1000000000000 : ℝ) (125096695223/250000000000 : ℝ) (500386780901/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16537/131072 : ℝ))) 3 (122167797/244140625 : ℝ) (500399296521/1000000000000 : ℝ) (125096695223/250000000000 : ℝ) (500386780901/1000000000000 : ℝ) (250196519351/500000000000 : ℝ) (500393038711/1000000000000 : ℝ) (250196519331/500000000000 : ℝ) (31274564917/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16537/131072 : ℝ))) 4 (250196519351/500000000000 : ℝ) (500393038711/1000000000000 : ℝ) (250196519331/500000000000 : ℝ) (31274564917/62500000000 : ℝ) (250196519341/500000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16537/131072 : ℝ))) 5 (250196519341/500000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16537/131072 : ℝ))) 6 (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16537/131072 : ℝ))) 7 (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16537/131072 : ℝ)) hmem 8 (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16537/131072 : ℝ))) hcmem 8 (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16537/131072 : ℝ)) (992160975589/1000000000000 : ℝ) (124020121949/125000000000 : ℝ) (500393038681/1000000000000 : ℝ) (125098259673/250000000000 : ℝ) (79222582469/100000000000 : ℝ) (792225824711/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0310_exp_lower
  have heNumeric : (1027451047397/500000000000 : ℝ)/4 ≤ Real.exp (-2664264626969/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451047397/500000000000 : ℝ)/4 ≤ Real.exp ((2067/16384 : ℝ)-(792225824711/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2067/16384 : ℝ) (16537/131072 : ℝ) (792225824711/1000000000000 : ℝ) (1027451047397/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0311; no trusted numerical premise.
theorem cover8_leaf0311_exp_radius : (124753807358249187/125000000000000000 : ℝ) ≤ Real.exp ((-8269/524288 : ℝ)/8) ∧ Real.exp ((-8269/524288 : ℝ)/8) ≤ (998030458865993497/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8269/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0311_exp_lower : (115014184020147219/125000000000000000 : ℝ) ≤ Real.exp ((-21314118973207/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314118973207/32000000000000 : ℝ)/8) ≤ (920113472161177753/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314118973207/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0311_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980393819/200000000000 : ℝ) ≤ 4*Real.exp (16537/131072 : ℝ)*Real.exp (-mu (radius 8 (8269/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410980393819/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8269/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0311_exp_radius
  have hrNumeric : (984351858721/1000000000000 : ℝ) ≤ Real.exp (-8269/524288 : ℝ) ∧ Real.exp (-8269/524288 : ℝ) ≤ (492175929361/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984351858721/1000000000000 : ℝ) ≤ (radius 8 (8269/65536 : ℝ)) ∧ (radius 8 (8269/65536 : ℝ)) ≤ (492175929361/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8269/65536 : ℝ)) (984351858721/1000000000000 : ℝ) (492175929361/500000000000 : ℝ) (176214126081/1000000000000 : ℝ) (176214126087/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8269/65536 : ℝ)) (984351858721/1000000000000 : ℝ) (492175929361/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8269/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984351858721/1000000000000 : ℝ) (492175929361/500000000000 : ℝ) (12402199117/12500000000 : ℝ) (992175929361/1000000000000 : ℝ) (62009067467/62500000000 : ℝ) (992145079473/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8269/65536 : ℝ)) 1 (12402199117/12500000000 : ℝ) (992175929361/1000000000000 : ℝ) (62009067467/62500000000 : ℝ) (992145079473/1000000000000 : ℝ) (31005015763/31250000000 : ℝ) (992160504417/1000000000000 : ℝ) (124020063037/125000000000 : ℝ) (496080252149/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8269/65536 : ℝ)) 2 (31005015763/31250000000 : ℝ) (992160504417/1000000000000 : ℝ) (124020063037/125000000000 : ℝ) (496080252149/500000000000 : ℝ) (248040126089/250000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8269/65536 : ℝ)) 3 (248040126089/250000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8269/65536 : ℝ)) 4 (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8269/65536 : ℝ)) 5 (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8269/65536 : ℝ)) 6 (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8269/65536 : ℝ)) 7 (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8269/65536 : ℝ))) (176214126081/1000000000000 : ℝ) (176214126087/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8269/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176214126081/1000000000000 : ℝ) (176214126087/1000000000000 : ℝ) (459458643/781250000 : ℝ) (147026765761/250000000000 : ℝ) (419778663203/1000000000000 : ℝ) (419778663211/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8269/65536 : ℝ))) 1 (459458643/781250000 : ℝ) (147026765761/250000000000 : ℝ) (419778663203/1000000000000 : ℝ) (419778663211/1000000000000 : ℝ) (503942863121/1000000000000 : ℝ) (62992857891/125000000000 : ℝ) (496864968319/1000000000000 : ℝ) (248432484163/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8269/65536 : ℝ))) 2 (503942863121/1000000000000 : ℝ) (62992857891/125000000000 : ℝ) (496864968319/1000000000000 : ℝ) (248432484163/500000000000 : ℝ) (12510097893/25000000000 : ℝ) (500403915727/1000000000000 : ℝ) (125097850381/250000000000 : ℝ) (125097850383/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8269/65536 : ℝ))) 3 (12510097893/25000000000 : ℝ) (500403915727/1000000000000 : ℝ) (125097850381/250000000000 : ℝ) (125097850383/250000000000 : ℝ) (250198829311/500000000000 : ℝ) (50039765863/100000000000 : ℝ) (250198829291/500000000000 : ℝ) (500397658591/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8269/65536 : ℝ))) 4 (250198829311/500000000000 : ℝ) (50039765863/100000000000 : ℝ) (250198829291/500000000000 : ℝ) (500397658591/1000000000000 : ℝ) (250198829301/500000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8269/65536 : ℝ))) 5 (250198829301/500000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8269/65536 : ℝ))) 6 (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8269/65536 : ℝ))) 7 (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8269/65536 : ℝ)) hmem 8 (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8269/65536 : ℝ))) hcmem 8 (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8269/65536 : ℝ)) (198432100871/200000000000 : ℝ) (496080252179/500000000000 : ℝ) (500397658601/1000000000000 : ℝ) (500397658611/1000000000000 : ℝ) (792233515257/1000000000000 : ℝ) (198058378819/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0311_exp_lower
  have heNumeric : (410980393819/200000000000 : ℝ)/4 ≤ Real.exp (-21314118973207/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980393819/200000000000 : ℝ)/4 ≤ Real.exp ((16537/131072 : ℝ)-(198058378819/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16537/131072 : ℝ) (8269/65536 : ℝ) (198058378819/250000000000 : ℝ) (410980393819/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0312; no trusted numerical premise.
theorem cover8_leaf0312_exp_radius : (249507584972874659/250000000000000000 : ℝ) ≤ Real.exp ((-16539/1048576 : ℝ)/8) ∧ Real.exp ((-16539/1048576 : ℝ)/8) ≤ (998030339891498637/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16539/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0312_exp_lower : (460056732580967849/500000000000000000 : ℝ) ≤ Real.exp ((-10657060460291/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657060460291/16000000000000 : ℝ)/8) ≤ (920113465161935699/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657060460291/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0312_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901844043/1000000000000 : ℝ) ≤ 4*Real.exp (8269/65536 : ℝ)*Real.exp (-mu (radius 8 (16539/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901844043/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16539/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0312_exp_radius
  have hrNumeric : (98435091997/100000000000 : ℝ) ≤ Real.exp (-16539/1048576 : ℝ) ∧ Real.exp (-16539/1048576 : ℝ) ≤ (984350919971/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98435091997/100000000000 : ℝ) ≤ (radius 8 (16539/131072 : ℝ)) ∧ (radius 8 (16539/131072 : ℝ)) ≤ (984350919971/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16539/131072 : ℝ)) (98435091997/100000000000 : ℝ) (984350919971/1000000000000 : ℝ) (11013710623/62500000000 : ℝ) (7048774799/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16539/131072 : ℝ)) (98435091997/100000000000 : ℝ) (984350919971/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16539/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98435091997/100000000000 : ℝ) (984350919971/1000000000000 : ℝ) (198435091997/200000000000 : ℝ) (496087729993/500000000000 : ℝ) (49607230319/50000000000 : ℝ) (496072303191/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16539/131072 : ℝ)) 1 (198435091997/200000000000 : ℝ) (496087729993/500000000000 : ℝ) (49607230319/50000000000 : ℝ) (496072303191/500000000000 : ℝ) (496080016591/500000000000 : ℝ) (31005001037/31250000000 : ℝ) (496080016531/500000000000 : ℝ) (198432006613/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16539/131072 : ℝ)) 2 (496080016591/500000000000 : ℝ) (31005001037/31250000000 : ℝ) (496080016531/500000000000 : ℝ) (198432006613/200000000000 : ℝ) (496080016561/500000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16539/131072 : ℝ)) 3 (496080016561/500000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16539/131072 : ℝ)) 4 (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16539/131072 : ℝ)) 5 (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16539/131072 : ℝ)) 6 (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16539/131072 : ℝ)) 7 (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16539/131072 : ℝ))) (11013710623/62500000000 : ℝ) (7048774799/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16539/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11013710623/62500000000 : ℝ) (7048774799/40000000000 : ℝ) (73513710623/125000000000 : ℝ) (147027421247/250000000000 : ℝ) (419784909171/1000000000000 : ℝ) (20989245459/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16539/131072 : ℝ))) 1 (73513710623/125000000000 : ℝ) (147027421247/250000000000 : ℝ) (419784909171/1000000000000 : ℝ) (20989245459/50000000000 : ℝ) (503947297077/1000000000000 : ℝ) (125986824271/250000000000 : ℝ) (31054360773/62500000000 : ℝ) (62108721547/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16539/131072 : ℝ))) 2 (503947297077/1000000000000 : ℝ) (125986824271/250000000000 : ℝ) (31054360773/62500000000 : ℝ) (62108721547/125000000000 : ℝ) (250204267361/500000000000 : ℝ) (50040853473/100000000000 : ℝ) (10007920439/20000000000 : ℝ) (500396021959/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16539/131072 : ℝ))) 3 (250204267361/500000000000 : ℝ) (50040853473/100000000000 : ℝ) (10007920439/20000000000 : ℝ) (500396021959/1000000000000 : ℝ) (7818785599/15625000000 : ℝ) (100080455669/200000000000 : ℝ) (62550284787/125000000000 : ℝ) (250201139153/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16539/131072 : ℝ))) 4 (7818785599/15625000000 : ℝ) (100080455669/200000000000 : ℝ) (62550284787/125000000000 : ℝ) (250201139153/500000000000 : ℝ) (125100569579/250000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16539/131072 : ℝ))) 5 (125100569579/250000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16539/131072 : ℝ))) 6 (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16539/131072 : ℝ))) 7 (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16539/131072 : ℝ)) hmem 8 (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16539/131072 : ℝ))) hcmem 8 (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16539/131072 : ℝ)) (992160033121/1000000000000 : ℝ) (1587456053/1600000000 : ℝ) (100080455663/200000000000 : ℝ) (250201139163/500000000000 : ℝ) (158448241101/200000000000 : ℝ) (396120602763/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0312_exp_lower
  have heNumeric : (2054901844043/1000000000000 : ℝ)/4 ≤ Real.exp (-10657060460291/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901844043/1000000000000 : ℝ)/4 ≤ Real.exp ((8269/65536 : ℝ)-(396120602763/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8269/65536 : ℝ) (16539/131072 : ℝ) (396120602763/500000000000 : ℝ) (2054901844043/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0313; no trusted numerical premise.
theorem cover8_leaf0313_exp_radius : (499015110458508979/500000000000000000 : ℝ) ≤ Real.exp ((-4135/262144 : ℝ)/8) ∧ Real.exp ((-4135/262144 : ℝ)/8) ≤ (998030220917017959/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4135/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0313_exp_lower : (920113458199958291/1000000000000000000 : ℝ) ≤ Real.exp ((-21314122857589/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314122857589/32000000000000 : ℝ)/8) ≤ (230028364549989573/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314122857589/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0313_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901719657/1000000000000 : ℝ) ≤ 4*Real.exp (16539/131072 : ℝ)*Real.exp (-mu (radius 8 (4135/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901719657/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4135/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0313_exp_radius
  have hrNumeric : (984349981221/1000000000000 : ℝ) ≤ Real.exp (-4135/262144 : ℝ) ∧ Real.exp (-4135/262144 : ℝ) ≤ (492174990611/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984349981221/1000000000000 : ℝ) ≤ (radius 8 (4135/32768 : ℝ)) ∧ (radius 8 (4135/32768 : ℝ)) ≤ (492174990611/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4135/32768 : ℝ)) (984349981221/1000000000000 : ℝ) (492174990611/500000000000 : ℝ) (44056153421/250000000000 : ℝ) (176224613691/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4135/32768 : ℝ)) (984349981221/1000000000000 : ℝ) (492174990611/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4135/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984349981221/1000000000000 : ℝ) (492174990611/500000000000 : ℝ) (99217499061/100000000000 : ℝ) (992174990611/1000000000000 : ℝ) (992144133289/1000000000000 : ℝ) (992144133291/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4135/32768 : ℝ)) 1 (99217499061/100000000000 : ℝ) (992174990611/1000000000000 : ℝ) (992144133289/1000000000000 : ℝ) (992144133291/1000000000000 : ℝ) (992159561949/1000000000000 : ℝ) (992159561951/1000000000000 : ℝ) (992159561829/1000000000000 : ℝ) (124019945229/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4135/32768 : ℝ)) 2 (992159561949/1000000000000 : ℝ) (992159561951/1000000000000 : ℝ) (992159561829/1000000000000 : ℝ) (124019945229/125000000000 : ℝ) (992159561889/1000000000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4135/32768 : ℝ)) 3 (992159561889/1000000000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4135/32768 : ℝ)) 4 (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4135/32768 : ℝ)) 5 (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4135/32768 : ℝ)) 6 (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4135/32768 : ℝ)) 7 (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4135/32768 : ℝ))) (44056153421/250000000000 : ℝ) (176224613691/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4135/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44056153421/250000000000 : ℝ) (176224613691/1000000000000 : ℝ) (294056153421/500000000000 : ℝ) (294056153423/500000000000 : ℝ) (209895577421/500000000000 : ℝ) (419791154851/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4135/32768 : ℝ))) 1 (294056153421/500000000000 : ℝ) (294056153423/500000000000 : ℝ) (209895577421/500000000000 : ℝ) (419791154851/1000000000000 : ℝ) (251975865421/500000000000 : ℝ) (503951730849/1000000000000 : ℝ) (7763665253/15625000000 : ℝ) (2484372881/5000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4135/32768 : ℝ))) 2 (251975865421/500000000000 : ℝ) (503951730849/1000000000000 : ℝ) (7763665253/15625000000 : ℝ) (2484372881/5000000000 : ℝ) (500413153517/1000000000000 : ℝ) (20016526141/40000000000 : ℝ) (500400642169/1000000000000 : ℝ) (500400642177/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4135/32768 : ℝ))) 3 (500413153517/1000000000000 : ℝ) (20016526141/40000000000 : ℝ) (500400642169/1000000000000 : ℝ) (500400642177/1000000000000 : ℝ) (500406897843/1000000000000 : ℝ) (500406897851/1000000000000 : ℝ) (500406897803/1000000000000 : ℝ) (125101724453/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4135/32768 : ℝ))) 4 (500406897843/1000000000000 : ℝ) (500406897851/1000000000000 : ℝ) (500406897803/1000000000000 : ℝ) (125101724453/250000000000 : ℝ) (500406897823/1000000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4135/32768 : ℝ))) 5 (500406897823/1000000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4135/32768 : ℝ))) 6 (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4135/32768 : ℝ))) 7 (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4135/32768 : ℝ)) hmem 8 (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4135/32768 : ℝ))) hcmem 8 (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4135/32768 : ℝ)) (31004986309/31250000000 : ℝ) (248039890473/250000000000 : ℝ) (250203448911/500000000000 : ℝ) (62550862229/125000000000 : ℝ) (99031111929/125000000000 : ℝ) (198062223863/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0313_exp_lower
  have heNumeric : (2054901719657/1000000000000 : ℝ)/4 ≤ Real.exp (-21314122857589/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901719657/1000000000000 : ℝ)/4 ≤ Real.exp ((16539/131072 : ℝ)-(198062223863/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16539/131072 : ℝ) (4135/32768 : ℝ) (198062223863/250000000000 : ℝ) (2054901719657/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0314; no trusted numerical premise.
theorem cover8_leaf0314_exp_radius : (124753762742818933/125000000000000000 : ℝ) ≤ Real.exp ((-16541/1048576 : ℝ)/8) ∧ Real.exp ((-16541/1048576 : ℝ)/8) ≤ (199606020388510293/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16541/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0314_exp_lower : (230028362818437587/250000000000000000 : ℝ) ≤ Real.exp ((-5328531196161/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328531196161/8000000000000 : ℝ)/8) ≤ (920113451273750349/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328531196161/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0314_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490159591/100000000000 : ℝ) ≤ 4*Real.exp (4135/32768 : ℝ)*Real.exp (-mu (radius 8 (16541/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (205490159591/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16541/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0314_exp_radius
  have hrNumeric : (123043630309/125000000000 : ℝ) ≤ Real.exp (-16541/1048576 : ℝ) ∧ Real.exp (-16541/1048576 : ℝ) ≤ (984349042473/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123043630309/125000000000 : ℝ) ≤ (radius 8 (16541/131072 : ℝ)) ∧ (radius 8 (16541/131072 : ℝ)) ≤ (984349042473/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16541/131072 : ℝ)) (123043630309/125000000000 : ℝ) (984349042473/1000000000000 : ℝ) (176229857239/1000000000000 : ℝ) (35245971449/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16541/131072 : ℝ)) (123043630309/125000000000 : ℝ) (984349042473/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16541/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123043630309/125000000000 : ℝ) (984349042473/1000000000000 : ℝ) (248043630309/250000000000 : ℝ) (992174521237/1000000000000 : ℝ) (496071830099/500000000000 : ℝ) (992143660199/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16541/131072 : ℝ)) 1 (248043630309/250000000000 : ℝ) (992174521237/1000000000000 : ℝ) (496071830099/500000000000 : ℝ) (992143660199/1000000000000 : ℝ) (992159090717/1000000000000 : ℝ) (496079545359/500000000000 : ℝ) (992159090597/1000000000000 : ℝ) (992159090599/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16541/131072 : ℝ)) 2 (992159090717/1000000000000 : ℝ) (496079545359/500000000000 : ℝ) (992159090597/1000000000000 : ℝ) (992159090599/1000000000000 : ℝ) (992159090657/1000000000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16541/131072 : ℝ)) 3 (992159090657/1000000000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16541/131072 : ℝ)) 4 (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16541/131072 : ℝ)) 5 (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16541/131072 : ℝ)) 6 (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16541/131072 : ℝ)) 7 (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16541/131072 : ℝ))) (176229857239/1000000000000 : ℝ) (35245971449/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16541/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176229857239/1000000000000 : ℝ) (35245971449/200000000000 : ℝ) (588114928619/1000000000000 : ℝ) (588114928623/1000000000000 : ℝ) (104949350057/250000000000 : ℝ) (419797400237/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16541/131072 : ℝ))) 1 (588114928619/1000000000000 : ℝ) (588114928623/1000000000000 : ℝ) (104949350057/250000000000 : ℝ) (419797400237/1000000000000 : ℝ) (503956164423/1000000000000 : ℝ) (50395616443/100000000000 : ℝ) (496879379799/1000000000000 : ℝ) (496879379807/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16541/131072 : ℝ))) 2 (503956164423/1000000000000 : ℝ) (50395616443/100000000000 : ℝ) (496879379799/1000000000000 : ℝ) (496879379807/1000000000000 : ℝ) (500417772111/1000000000000 : ℝ) (500417772119/1000000000000 : ℝ) (250202631093/500000000000 : ℝ) (100081052439/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16541/131072 : ℝ))) 3 (500417772111/1000000000000 : ℝ) (500417772119/1000000000000 : ℝ) (250202631093/500000000000 : ℝ) (100081052439/200000000000 : ℝ) (125102879287/250000000000 : ℝ) (500411517157/1000000000000 : ℝ) (500411517109/1000000000000 : ℝ) (250205758559/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16541/131072 : ℝ))) 4 (125102879287/250000000000 : ℝ) (500411517157/1000000000000 : ℝ) (500411517109/1000000000000 : ℝ) (250205758559/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16541/131072 : ℝ))) 5 (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16541/131072 : ℝ))) 6 (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16541/131072 : ℝ))) 7 (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16541/131072 : ℝ)) hmem 8 (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16541/131072 : ℝ))) hcmem 8 (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16541/131072 : ℝ)) (31004971583/31250000000 : ℝ) (992159090659/1000000000000 : ℝ) (62551439641/125000000000 : ℝ) (250205758569/500000000000 : ℝ) (99032073131/125000000000 : ℝ) (792256585067/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0314_exp_lower
  have heNumeric : (205490159591/100000000000 : ℝ)/4 ≤ Real.exp (-5328531196161/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490159591/100000000000 : ℝ)/4 ≤ Real.exp ((4135/32768 : ℝ)-(792256585067/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4135/32768 : ℝ) (16541/131072 : ℝ) (792256585067/1000000000000 : ℝ) (205490159591/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0315; no trusted numerical premise.
theorem cover8_leaf0315_exp_radius : (998029982968099153/1000000000000000000 : ℝ) ≤ Real.exp ((-8271/524288 : ℝ)/8) ∧ Real.exp ((-8271/524288 : ℝ)/8) ≤ (499014991484049577/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8271/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0315_exp_lower : (920113444383886937/1000000000000000000 : ℝ) ≤ Real.exp ((-21314126701587/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314126701587/32000000000000 : ℝ)/8) ≤ (460056722191943469/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314126701587/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0315_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725368203/250000000000 : ℝ) ≤ 4*Real.exp (16541/131072 : ℝ)*Real.exp (-mu (radius 8 (8271/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513725368203/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8271/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0315_exp_radius
  have hrNumeric : (246087025931/250000000000 : ℝ) ≤ Real.exp (-8271/524288 : ℝ) ∧ Real.exp (-8271/524288 : ℝ) ≤ (39373924149/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246087025931/250000000000 : ℝ) ≤ (radius 8 (8271/65536 : ℝ)) ∧ (radius 8 (8271/65536 : ℝ)) ≤ (39373924149/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8271/65536 : ℝ)) (246087025931/250000000000 : ℝ) (39373924149/40000000000 : ℝ) (88117550313/500000000000 : ℝ) (176235100633/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8271/65536 : ℝ)) (246087025931/250000000000 : ℝ) (39373924149/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8271/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246087025931/250000000000 : ℝ) (39373924149/40000000000 : ℝ) (496087025931/500000000000 : ℝ) (992174051863/1000000000000 : ℝ) (992143187107/1000000000000 : ℝ) (992143187109/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8271/65536 : ℝ)) 1 (496087025931/500000000000 : ℝ) (992174051863/1000000000000 : ℝ) (992143187107/1000000000000 : ℝ) (992143187109/1000000000000 : ℝ) (248039654871/250000000000 : ℝ) (496079309743/500000000000 : ℝ) (248039654841/250000000000 : ℝ) (496079309683/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8271/65536 : ℝ)) 2 (248039654871/250000000000 : ℝ) (496079309743/500000000000 : ℝ) (248039654841/250000000000 : ℝ) (496079309683/500000000000 : ℝ) (31004956857/31250000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8271/65536 : ℝ)) 3 (31004956857/31250000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8271/65536 : ℝ)) 4 (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8271/65536 : ℝ)) 5 (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8271/65536 : ℝ)) 6 (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8271/65536 : ℝ)) 7 (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8271/65536 : ℝ))) (88117550313/500000000000 : ℝ) (176235100633/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8271/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88117550313/500000000000 : ℝ) (176235100633/1000000000000 : ℝ) (588117550313/1000000000000 : ℝ) (588117550317/1000000000000 : ℝ) (209901822661/500000000000 : ℝ) (419803645331/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8271/65536 : ℝ))) 1 (588117550313/1000000000000 : ℝ) (588117550317/1000000000000 : ℝ) (209901822661/500000000000 : ℝ) (419803645331/1000000000000 : ℝ) (503960597817/1000000000000 : ℝ) (7874384341/15625000000 : ℝ) (31055261449/62500000000 : ℝ) (62110522899/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8271/65536 : ℝ))) 2 (503960597817/1000000000000 : ℝ) (7874384341/15625000000 : ℝ) (31055261449/62500000000 : ℝ) (62110522899/125000000000 : ℝ) (1000844781/2000000000 : ℝ) (125105597627/250000000000 : ℝ) (500409881999/1000000000000 : ℝ) (62551235251/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8271/65536 : ℝ))) 3 (1000844781/2000000000 : ℝ) (125105597627/250000000000 : ℝ) (500409881999/1000000000000 : ℝ) (62551235251/125000000000 : ℝ) (500416136249/1000000000000 : ℝ) (250208068129/500000000000 : ℝ) (50041613621/100000000000 : ℝ) (500416136219/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8271/65536 : ℝ))) 4 (500416136249/1000000000000 : ℝ) (250208068129/500000000000 : ℝ) (50041613621/100000000000 : ℝ) (500416136219/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8271/65536 : ℝ))) 5 (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8271/65536 : ℝ))) 6 (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8271/65536 : ℝ))) 7 (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8271/65536 : ℝ)) hmem 8 (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8271/65536 : ℝ))) hcmem 8 (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8271/65536 : ℝ)) (992158619423/1000000000000 : ℝ) (496079309713/500000000000 : ℝ) (500416136229/1000000000000 : ℝ) (500416136239/1000000000000 : ℝ) (792264274347/1000000000000 : ℝ) (396132137183/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0315_exp_lower
  have heNumeric : (513725368203/250000000000 : ℝ)/4 ≤ Real.exp (-21314126701587/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725368203/250000000000 : ℝ)/4 ≤ Real.exp ((16541/131072 : ℝ)-(396132137183/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16541/131072 : ℝ) (8271/65536 : ℝ) (396132137183/500000000000 : ℝ) (513725368203/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0316; no trusted numerical premise.
theorem cover8_leaf0316_exp_radius : (31188433249801907/31250000000000000 : ℝ) ≤ Real.exp ((-16543/1048576 : ℝ)/8) ∧ Real.exp ((-16543/1048576 : ℝ)/8) ≤ (39921194559746441/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16543/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0316_exp_lower : (920113437530138031/1000000000000000000 : ℝ) ≤ Real.exp ((-10657064304241/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657064304241/16000000000000 : ℝ)/8) ≤ (57507089845633627/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657064304241/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0316_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901350359/1000000000000 : ℝ) ≤ 4*Real.exp (8271/65536 : ℝ)*Real.exp (-mu (radius 8 (16543/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901350359/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16543/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0316_exp_radius
  have hrNumeric : (984347164977/1000000000000 : ℝ) ≤ Real.exp (-16543/1048576 : ℝ) ∧ Real.exp (-16543/1048576 : ℝ) ≤ (492173582489/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984347164977/1000000000000 : ℝ) ≤ (radius 8 (16543/131072 : ℝ)) ∧ (radius 8 (16543/131072 : ℝ)) ≤ (492173582489/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16543/131072 : ℝ)) (984347164977/1000000000000 : ℝ) (492173582489/500000000000 : ℝ) (22030042981/125000000000 : ℝ) (88120171927/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16543/131072 : ℝ)) (984347164977/1000000000000 : ℝ) (492173582489/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16543/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984347164977/1000000000000 : ℝ) (492173582489/500000000000 : ℝ) (124021697811/125000000000 : ℝ) (992173582489/1000000000000 : ℝ) (31004459813/31250000000 : ℝ) (496071357009/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16543/131072 : ℝ)) 1 (124021697811/125000000000 : ℝ) (992173582489/1000000000000 : ℝ) (31004459813/31250000000 : ℝ) (496071357009/500000000000 : ℝ) (248039537063/250000000000 : ℝ) (496079074127/500000000000 : ℝ) (992158148131/1000000000000 : ℝ) (496079074067/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16543/131072 : ℝ)) 2 (248039537063/250000000000 : ℝ) (496079074127/500000000000 : ℝ) (992158148131/1000000000000 : ℝ) (496079074067/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16543/131072 : ℝ)) 3 (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16543/131072 : ℝ)) 4 (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16543/131072 : ℝ)) 5 (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16543/131072 : ℝ)) 6 (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16543/131072 : ℝ)) 7 (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16543/131072 : ℝ))) (22030042981/125000000000 : ℝ) (88120171927/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16543/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22030042981/125000000000 : ℝ) (88120171927/500000000000 : ℝ) (147030042981/250000000000 : ℝ) (588120171927/1000000000000 : ℝ) (209904945063/500000000000 : ℝ) (209904945067/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16543/131072 : ℝ))) 1 (147030042981/250000000000 : ℝ) (588120171927/1000000000000 : ℝ) (209904945063/500000000000 : ℝ) (209904945067/500000000000 : ℝ) (20158601241/40000000000 : ℝ) (503965031031/1000000000000 : ℝ) (9937779727/20000000000 : ℝ) (496888986357/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16543/131072 : ℝ))) 2 (20158601241/40000000000 : ℝ) (503965031031/1000000000000 : ℝ) (9937779727/20000000000 : ℝ) (496888986357/1000000000000 : ℝ) (500427008687/1000000000000 : ℝ) (250213504347/500000000000 : ℝ) (50041450161/100000000000 : ℝ) (500414501617/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16543/131072 : ℝ))) 3 (500427008687/1000000000000 : ℝ) (250213504347/500000000000 : ℝ) (50041450161/100000000000 : ℝ) (500414501617/1000000000000 : ℝ) (125105188787/250000000000 : ℝ) (125105188789/250000000000 : ℝ) (500420755109/1000000000000 : ℝ) (500420755117/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16543/131072 : ℝ))) 4 (125105188787/250000000000 : ℝ) (125105188789/250000000000 : ℝ) (500420755109/1000000000000 : ℝ) (500420755117/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16543/131072 : ℝ))) 5 (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16543/131072 : ℝ))) 6 (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16543/131072 : ℝ))) 7 (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16543/131072 : ℝ)) hmem 8 (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16543/131072 : ℝ))) hcmem 8 (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16543/131072 : ℝ)) (992158148191/1000000000000 : ℝ) (496079074097/500000000000 : ℝ) (62552594391/125000000000 : ℝ) (500420755137/1000000000000 : ℝ) (792271963333/1000000000000 : ℝ) (792271963351/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0316_exp_lower
  have heNumeric : (2054901350359/1000000000000 : ℝ)/4 ≤ Real.exp (-10657064304241/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901350359/1000000000000 : ℝ)/4 ≤ Real.exp ((8271/65536 : ℝ)-(792271963351/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8271/65536 : ℝ) (16543/131072 : ℝ) (792271963351/1000000000000 : ℝ) (2054901350359/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0317; no trusted numerical premise.
theorem cover8_leaf0317_exp_radius : (499014872509618539/500000000000000000 : ℝ) ≤ Real.exp ((-517/32768 : ℝ)/8) ∧ Real.exp ((-517/32768 : ℝ)/8) ≤ (998029745019237079/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-517/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0317_exp_lower : (184022686142592737/200000000000000000 : ℝ) ≤ Real.exp ((-21314130505201/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314130505201/32000000000000 : ℝ)/8) ≤ (460056715356481843/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314130505201/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0317_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (25686265357/12500000000 : ℝ) ≤ 4*Real.exp (16543/131072 : ℝ)*Real.exp (-mu (radius 8 (517/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (25686265357/12500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (517/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0317_exp_radius
  have hrNumeric : (984346226231/1000000000000 : ℝ) ≤ Real.exp (-517/32768 : ℝ) ∧ Real.exp (-517/32768 : ℝ) ≤ (123043278279/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984346226231/1000000000000 : ℝ) ≤ (radius 8 (517/4096 : ℝ)) ∧ (radius 8 (517/4096 : ℝ)) ≤ (123043278279/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (517/4096 : ℝ)) (984346226231/1000000000000 : ℝ) (123043278279/125000000000 : ℝ) (176245586903/1000000000000 : ℝ) (176245586909/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (517/4096 : ℝ)) (984346226231/1000000000000 : ℝ) (123043278279/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (517/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984346226231/1000000000000 : ℝ) (123043278279/125000000000 : ℝ) (198434622623/200000000000 : ℝ) (248043278279/250000000000 : ℝ) (496071120463/500000000000 : ℝ) (31004445029/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (517/4096 : ℝ)) 1 (198434622623/200000000000 : ℝ) (248043278279/250000000000 : ℝ) (496071120463/500000000000 : ℝ) (31004445029/31250000000 : ℝ) (49607883851/50000000000 : ℝ) (496078838511/500000000000 : ℝ) (9921576769/10000000000 : ℝ) (496078838451/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (517/4096 : ℝ)) 2 (49607883851/50000000000 : ℝ) (496078838511/500000000000 : ℝ) (9921576769/10000000000 : ℝ) (496078838451/500000000000 : ℝ) (6200985481/6250000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (517/4096 : ℝ)) 3 (6200985481/6250000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (517/4096 : ℝ)) 4 (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (517/4096 : ℝ)) 5 (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (517/4096 : ℝ)) 6 (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (517/4096 : ℝ)) 7 (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (517/4096 : ℝ))) (176245586903/1000000000000 : ℝ) (176245586909/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (517/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176245586903/1000000000000 : ℝ) (176245586909/1000000000000 : ℝ) (588122793451/1000000000000 : ℝ) (117624558691/200000000000 : ℝ) (209908067319/500000000000 : ℝ) (209908067323/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (517/4096 : ℝ))) 1 (588122793451/1000000000000 : ℝ) (117624558691/200000000000 : ℝ) (209908067319/500000000000 : ℝ) (209908067323/500000000000 : ℝ) (125992366011/250000000000 : ℝ) (503969464051/1000000000000 : ℝ) (248446894647/500000000000 : ℝ) (496893789301/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (517/4096 : ℝ))) 2 (125992366011/250000000000 : ℝ) (503969464051/1000000000000 : ℝ) (248446894647/500000000000 : ℝ) (496893789301/1000000000000 : ℝ) (500431626669/1000000000000 : ℝ) (125107906669/250000000000 : ℝ) (250209560507/500000000000 : ℝ) (250209560511/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (517/4096 : ℝ))) 3 (500431626669/1000000000000 : ℝ) (125107906669/250000000000 : ℝ) (250209560507/500000000000 : ℝ) (250209560511/500000000000 : ℝ) (500425373841/1000000000000 : ℝ) (500425373849/1000000000000 : ℝ) (250212686901/500000000000 : ℝ) (50042537381/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (517/4096 : ℝ))) 4 (500425373841/1000000000000 : ℝ) (500425373849/1000000000000 : ℝ) (250212686901/500000000000 : ℝ) (50042537381/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (517/4096 : ℝ))) 5 (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (517/4096 : ℝ))) 6 (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (517/4096 : ℝ))) 7 (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (517/4096 : ℝ)) hmem 8 (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (517/4096 : ℝ))) hcmem 8 (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (517/4096 : ℝ)) (992157676959/1000000000000 : ℝ) (496078838481/500000000000 : ℝ) (500425373821/1000000000000 : ℝ) (50042537383/100000000000 : ℝ) (198069913/250000000 : ℝ) (396139826009/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0317_exp_lower
  have heNumeric : (25686265357/12500000000 : ℝ)/4 ≤ Real.exp (-21314130505201/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (25686265357/12500000000 : ℝ)/4 ≤ Real.exp ((16543/131072 : ℝ)-(396139826009/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16543/131072 : ℝ) (517/4096 : ℝ) (396139826009/500000000000 : ℝ) (25686265357/12500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0318; no trusted numerical premise.
theorem cover8_leaf0318_exp_radius : (249507406511206829/250000000000000000 : ℝ) ≤ Real.exp ((-16545/1048576 : ℝ)/8) ∧ Real.exp ((-16545/1048576 : ℝ)/8) ≤ (998029626044827317/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16545/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0318_exp_lower : (230028355982803439/250000000000000000 : ℝ) ≤ Real.exp ((-166516659313/250000000000 : ℝ)/8) ∧ Real.exp ((-166516659313/250000000000 : ℝ)/8) ≤ (920113423931213757/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166516659313/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0318_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450553697/500000000000 : ℝ) ≤ 4*Real.exp (517/4096 : ℝ)*Real.exp (-mu (radius 8 (16545/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450553697/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16545/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0318_exp_radius
  have hrNumeric : (196869057497/200000000000 : ℝ) ≤ Real.exp (-16545/1048576 : ℝ) ∧ Real.exp (-16545/1048576 : ℝ) ≤ (492172643743/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196869057497/200000000000 : ℝ) ≤ (radius 8 (16545/131072 : ℝ)) ∧ (radius 8 (16545/131072 : ℝ)) ≤ (492172643743/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16545/131072 : ℝ)) (196869057497/200000000000 : ℝ) (492172643743/500000000000 : ℝ) (44062707449/250000000000 : ℝ) (176250829803/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16545/131072 : ℝ)) (196869057497/200000000000 : ℝ) (492172643743/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16545/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196869057497/200000000000 : ℝ) (492172643743/500000000000 : ℝ) (496086321871/500000000000 : ℝ) (992172643743/1000000000000 : ℝ) (248035441959/250000000000 : ℝ) (992141767837/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16545/131072 : ℝ)) 1 (496086321871/500000000000 : ℝ) (992172643743/1000000000000 : ℝ) (248035441959/250000000000 : ℝ) (992141767837/1000000000000 : ℝ) (992157205789/1000000000000 : ℝ) (99215720579/100000000000 : ℝ) (248039301417/250000000000 : ℝ) (99215720567/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16545/131072 : ℝ)) 2 (992157205789/1000000000000 : ℝ) (99215720579/100000000000 : ℝ) (248039301417/250000000000 : ℝ) (99215720567/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16545/131072 : ℝ)) 3 (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16545/131072 : ℝ)) 4 (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16545/131072 : ℝ)) 5 (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16545/131072 : ℝ)) 6 (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16545/131072 : ℝ)) 7 (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16545/131072 : ℝ))) (44062707449/250000000000 : ℝ) (176250829803/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16545/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44062707449/250000000000 : ℝ) (176250829803/1000000000000 : ℝ) (294062707449/500000000000 : ℝ) (294062707451/500000000000 : ℝ) (83964475773/200000000000 : ℝ) (209911189437/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16545/131072 : ℝ))) 1 (294062707449/500000000000 : ℝ) (294062707451/500000000000 : ℝ) (83964475773/200000000000 : ℝ) (209911189437/500000000000 : ℝ) (503973896881/1000000000000 : ℝ) (62996737111/125000000000 : ℝ) (496898592021/1000000000000 : ℝ) (49689859203/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16545/131072 : ℝ))) 2 (503973896881/1000000000000 : ℝ) (62996737111/125000000000 : ℝ) (496898592021/1000000000000 : ℝ) (49689859203/100000000000 : ℝ) (500436244451/1000000000000 : ℝ) (500436244459/1000000000000 : ℝ) (500423740219/1000000000000 : ℝ) (125105935057/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16545/131072 : ℝ))) 3 (500436244451/1000000000000 : ℝ) (500436244459/1000000000000 : ℝ) (500423740219/1000000000000 : ℝ) (125105935057/250000000000 : ℝ) (100085998467/200000000000 : ℝ) (62553749043/125000000000 : ℝ) (100085998459/200000000000 : ℝ) (100085998461/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16545/131072 : ℝ))) 4 (100085998467/200000000000 : ℝ) (62553749043/125000000000 : ℝ) (100085998459/200000000000 : ℝ) (100085998461/200000000000 : ℝ) (100085998463/200000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16545/131072 : ℝ))) 5 (100085998463/200000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16545/131072 : ℝ))) 6 (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16545/131072 : ℝ))) 7 (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16545/131072 : ℝ)) hmem 8 (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16545/131072 : ℝ))) hcmem 8 (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16545/131072 : ℝ)) (31004912679/31250000000 : ℝ) (99215720573/100000000000 : ℝ) (250214996157/500000000000 : ℝ) (20017199693/40000000000 : ℝ) (792287340357/1000000000000 : ℝ) (792287340377/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0318_exp_lower
  have heNumeric : (1027450553697/500000000000 : ℝ)/4 ≤ Real.exp (-166516659313/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450553697/500000000000 : ℝ)/4 ≤ Real.exp ((517/4096 : ℝ)-(792287340377/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (517/4096 : ℝ) (16545/131072 : ℝ) (792287340377/1000000000000 : ℝ) (1027450553697/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0319; no trusted numerical premise.
theorem cover8_leaf0319_exp_radius : (124753688383803967/125000000000000000 : ℝ) ≤ Real.exp ((-8273/524288 : ℝ)/8) ∧ Real.exp ((-8273/524288 : ℝ)/8) ≤ (998029507070431737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8273/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0319_exp_lower : (92011341718672847/100000000000000000 : ℝ) ≤ Real.exp ((-21314134268559/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314134268559/32000000000000 : ℝ)/8) ≤ (920113417186728471/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314134268559/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0319_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450493447/500000000000 : ℝ) ≤ 4*Real.exp (16545/131072 : ℝ)*Real.exp (-mu (radius 8 (8273/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450493447/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8273/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0319_exp_radius
  have hrNumeric : (984344348741/1000000000000 : ℝ) ≤ Real.exp (-8273/524288 : ℝ) ∧ Real.exp (-8273/524288 : ℝ) ≤ (492172174371/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984344348741/1000000000000 : ℝ) ≤ (radius 8 (8273/65536 : ℝ)) ∧ (radius 8 (8273/65536 : ℝ)) ≤ (492172174371/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8273/65536 : ℝ)) (984344348741/1000000000000 : ℝ) (492172174371/500000000000 : ℝ) (88128036259/500000000000 : ℝ) (7050242901/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8273/65536 : ℝ)) (984344348741/1000000000000 : ℝ) (492172174371/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8273/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984344348741/1000000000000 : ℝ) (492172174371/500000000000 : ℝ) (99217217437/100000000000 : ℝ) (992172174371/1000000000000 : ℝ) (496070647373/500000000000 : ℝ) (992141294747/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8273/65536 : ℝ)) 1 (99217217437/100000000000 : ℝ) (992172174371/1000000000000 : ℝ) (496070647373/500000000000 : ℝ) (992141294747/1000000000000 : ℝ) (496078367279/500000000000 : ℝ) (992156734559/1000000000000 : ℝ) (992156734437/1000000000000 : ℝ) (992156734439/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8273/65536 : ℝ)) 2 (496078367279/500000000000 : ℝ) (992156734559/1000000000000 : ℝ) (992156734437/1000000000000 : ℝ) (992156734439/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8273/65536 : ℝ)) 3 (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8273/65536 : ℝ)) 4 (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8273/65536 : ℝ)) 5 (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8273/65536 : ℝ)) 6 (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8273/65536 : ℝ)) 7 (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8273/65536 : ℝ))) (88128036259/500000000000 : ℝ) (7050242901/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8273/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88128036259/500000000000 : ℝ) (7050242901/40000000000 : ℝ) (588128036259/1000000000000 : ℝ) (588128036263/1000000000000 : ℝ) (83965724559/200000000000 : ℝ) (104957155701/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8273/65536 : ℝ))) 1 (588128036259/1000000000000 : ℝ) (588128036263/1000000000000 : ℝ) (83965724559/200000000000 : ℝ) (104957155701/250000000000 : ℝ) (503978329527/1000000000000 : ℝ) (251989164767/500000000000 : ℝ) (124225848631/250000000000 : ℝ) (124225848633/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8273/65536 : ℝ))) 2 (503978329527/1000000000000 : ℝ) (251989164767/500000000000 : ℝ) (124225848631/250000000000 : ℝ) (124225848633/250000000000 : ℝ) (20017634481/40000000000 : ℝ) (500440862033/1000000000000 : ℝ) (31276772451/62500000000 : ℝ) (20017134369/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8273/65536 : ℝ))) 3 (20017634481/40000000000 : ℝ) (500440862033/1000000000000 : ℝ) (31276772451/62500000000 : ℝ) (20017134369/40000000000 : ℝ) (25021730531/50000000000 : ℝ) (500434610629/1000000000000 : ℝ) (500434610581/1000000000000 : ℝ) (50043461059/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8273/65536 : ℝ))) 4 (25021730531/50000000000 : ℝ) (500434610629/1000000000000 : ℝ) (500434610581/1000000000000 : ℝ) (50043461059/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8273/65536 : ℝ))) 5 (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8273/65536 : ℝ))) 6 (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8273/65536 : ℝ))) 7 (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8273/65536 : ℝ)) hmem 8 (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8273/65536 : ℝ))) hcmem 8 (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8273/65536 : ℝ)) (992156734497/1000000000000 : ℝ) (992156734499/1000000000000 : ℝ) (2502173053/5000000000 : ℝ) (50043461061/100000000000 : ℝ) (396147514197/500000000000 : ℝ) (198073757103/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0319_exp_lower
  have heNumeric : (1027450493447/500000000000 : ℝ)/4 ≤ Real.exp (-21314134268559/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450493447/500000000000 : ℝ)/4 ≤ Real.exp ((16545/131072 : ℝ)-(198073757103/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16545/131072 : ℝ) (8273/65536 : ℝ) (198073757103/250000000000 : ℝ) (1027450493447/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0320; no trusted numerical premise.
theorem cover8_leaf0320_exp_radius : (499014694048025169/500000000000000000 : ℝ) ≤ Real.exp ((-16547/1048576 : ℝ)/8) ∧ Real.exp ((-16547/1048576 : ℝ)/8) ≤ (998029388096050339/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16547/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0320_exp_lower : (115014176309837841/125000000000000000 : ℝ) ≤ Real.exp ((-2131413613491/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131413613491/3200000000000 : ℝ)/8) ≤ (920113410478702729/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131413613491/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0320_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980173409/200000000000 : ℝ) ≤ 4*Real.exp (8273/65536 : ℝ)*Real.exp (-mu (radius 8 (16547/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980173409/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16547/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0320_exp_radius
  have hrNumeric : (492171704999/500000000000 : ℝ) ≤ Real.exp (-16547/1048576 : ℝ) ∧ Real.exp (-16547/1048576 : ℝ) ≤ (984343409999/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492171704999/500000000000 : ℝ) ≤ (radius 8 (16547/131072 : ℝ)) ∧ (radius 8 (16547/131072 : ℝ)) ≤ (984343409999/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16547/131072 : ℝ)) (492171704999/500000000000 : ℝ) (984343409999/1000000000000 : ℝ) (176261315073/1000000000000 : ℝ) (4406532877/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16547/131072 : ℝ)) (492171704999/500000000000 : ℝ) (984343409999/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16547/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492171704999/500000000000 : ℝ) (984343409999/1000000000000 : ℝ) (992171704999/1000000000000 : ℝ) (198434341/200000000 : ℝ) (124017602707/125000000000 : ℝ) (496070410829/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16547/131072 : ℝ)) 1 (992171704999/1000000000000 : ℝ) (198434341/200000000 : ℝ) (124017602707/125000000000 : ℝ) (496070410829/500000000000 : ℝ) (992156263327/1000000000000 : ℝ) (992156263329/1000000000000 : ℝ) (992156263207/1000000000000 : ℝ) (992156263209/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16547/131072 : ℝ)) 2 (992156263327/1000000000000 : ℝ) (992156263329/1000000000000 : ℝ) (992156263207/1000000000000 : ℝ) (992156263209/1000000000000 : ℝ) (992156263267/1000000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16547/131072 : ℝ)) 3 (992156263267/1000000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16547/131072 : ℝ)) 4 (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16547/131072 : ℝ)) 5 (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16547/131072 : ℝ)) 6 (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16547/131072 : ℝ)) 7 (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16547/131072 : ℝ))) (176261315073/1000000000000 : ℝ) (4406532877/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16547/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176261315073/1000000000000 : ℝ) (4406532877/25000000000 : ℝ) (2297385381/3906250000 : ℝ) (29406532877/50000000000 : ℝ) (419834866433/1000000000000 : ℝ) (209917433221/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16547/131072 : ℝ))) 1 (2297385381/3906250000 : ℝ) (29406532877/50000000000 : ℝ) (419834866433/1000000000000 : ℝ) (209917433221/500000000000 : ℝ) (246085333/488281250 : ℝ) (503982761991/1000000000000 : ℝ) (124227049201/250000000000 : ℝ) (124227049203/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16547/131072 : ℝ))) 2 (246085333/488281250 : ℝ) (503982761991/1000000000000 : ℝ) (124227049201/250000000000 : ℝ) (124227049203/250000000000 : ℝ) (250222739697/500000000000 : ℝ) (250222739701/500000000000 : ℝ) (500432978007/1000000000000 : ℝ) (15638530563/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16547/131072 : ℝ))) 3 (250222739697/500000000000 : ℝ) (250222739701/500000000000 : ℝ) (500432978007/1000000000000 : ℝ) (15638530563/31250000000 : ℝ) (5004392287/10000000000 : ℝ) (500439228709/1000000000000 : ℝ) (500439228661/1000000000000 : ℝ) (50043922867/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16547/131072 : ℝ))) 4 (5004392287/10000000000 : ℝ) (500439228709/1000000000000 : ℝ) (500439228661/1000000000000 : ℝ) (50043922867/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16547/131072 : ℝ))) 5 (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16547/131072 : ℝ))) 6 (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16547/131072 : ℝ))) 7 (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16547/131072 : ℝ)) hmem 8 (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16547/131072 : ℝ))) hcmem 8 (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16547/131072 : ℝ)) (496078131633/500000000000 : ℝ) (992156263269/1000000000000 : ℝ) (12510980717/25000000000 : ℝ) (50043922869/100000000000 : ℝ) (792302716111/1000000000000 : ℝ) (79230271613/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0320_exp_lower
  have heNumeric : (410980173409/200000000000 : ℝ)/4 ≤ Real.exp (-2131413613491/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980173409/200000000000 : ℝ)/4 ≤ Real.exp ((8273/65536 : ℝ)-(79230271613/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8273/65536 : ℝ) (16547/131072 : ℝ) (79230271613/100000000000 : ℝ) (410980173409/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0321; no trusted numerical premise.
theorem cover8_leaf0321_exp_radius : (249507317280420781/250000000000000000 : ℝ) ≤ Real.exp ((-4137/262144 : ℝ)/8) ∧ Real.exp ((-4137/262144 : ℝ)/8) ≤ (1596846830594693/1600000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4137/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0321_exp_lower : (920113403806101401/1000000000000000000 : ℝ) ≤ Real.exp ((-4262827598281/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262827598281/6400000000000 : ℝ)/8) ≤ (460056701903050701/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262827598281/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0321_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900747829/1000000000000 : ℝ) ≤ 4*Real.exp (16547/131072 : ℝ)*Real.exp (-mu (radius 8 (4137/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900747829/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4137/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0321_exp_radius
  have hrNumeric : (196868494251/200000000000 : ℝ) ≤ Real.exp (-4137/262144 : ℝ) ∧ Real.exp (-4137/262144 : ℝ) ≤ (123042808907/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196868494251/200000000000 : ℝ) ≤ (radius 8 (4137/32768 : ℝ)) ∧ (radius 8 (4137/32768 : ℝ)) ≤ (123042808907/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4137/32768 : ℝ)) (196868494251/200000000000 : ℝ) (123042808907/125000000000 : ℝ) (44066639367/250000000000 : ℝ) (88133278737/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4137/32768 : ℝ)) (196868494251/200000000000 : ℝ) (123042808907/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4137/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196868494251/200000000000 : ℝ) (123042808907/125000000000 : ℝ) (992171235627/1000000000000 : ℝ) (248042808907/250000000000 : ℝ) (992140348567/1000000000000 : ℝ) (124017543571/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4137/32768 : ℝ)) 1 (992171235627/1000000000000 : ℝ) (248042808907/250000000000 : ℝ) (992140348567/1000000000000 : ℝ) (124017543571/125000000000 : ℝ) (992155792097/1000000000000 : ℝ) (496077896049/500000000000 : ℝ) (124019473997/125000000000 : ℝ) (496077895989/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4137/32768 : ℝ)) 2 (992155792097/1000000000000 : ℝ) (496077896049/500000000000 : ℝ) (124019473997/125000000000 : ℝ) (496077895989/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4137/32768 : ℝ)) 3 (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4137/32768 : ℝ)) 4 (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4137/32768 : ℝ)) 5 (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4137/32768 : ℝ)) 6 (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4137/32768 : ℝ)) 7 (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4137/32768 : ℝ))) (44066639367/250000000000 : ℝ) (88133278737/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4137/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44066639367/250000000000 : ℝ) (88133278737/500000000000 : ℝ) (294066639367/500000000000 : ℝ) (588133278737/1000000000000 : ℝ) (419841109787/1000000000000 : ℝ) (104960277449/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4137/32768 : ℝ))) 1 (294066639367/500000000000 : ℝ) (588133278737/1000000000000 : ℝ) (419841109787/1000000000000 : ℝ) (104960277449/250000000000 : ℝ) (25199359713/50000000000 : ℝ) (503987194267/1000000000000 : ℝ) (49691299887/100000000000 : ℝ) (496912998877/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4137/32768 : ℝ))) 2 (25199359713/50000000000 : ℝ) (503987194267/1000000000000 : ℝ) (49691299887/100000000000 : ℝ) (496912998877/1000000000000 : ℝ) (100090019313/200000000000 : ℝ) (125112524143/250000000000 : ℝ) (500437596601/1000000000000 : ℝ) (500437596609/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4137/32768 : ℝ))) 3 (100090019313/200000000000 : ℝ) (125112524143/250000000000 : ℝ) (500437596601/1000000000000 : ℝ) (500437596609/1000000000000 : ℝ) (500443846583/1000000000000 : ℝ) (500443846591/1000000000000 : ℝ) (500443846543/1000000000000 : ℝ) (62555480819/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4137/32768 : ℝ))) 4 (500443846583/1000000000000 : ℝ) (500443846591/1000000000000 : ℝ) (500443846543/1000000000000 : ℝ) (62555480819/125000000000 : ℝ) (500443846563/1000000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4137/32768 : ℝ))) 5 (500443846563/1000000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4137/32768 : ℝ))) 6 (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4137/32768 : ℝ))) 7 (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4137/32768 : ℝ)) hmem 8 (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4137/32768 : ℝ))) hcmem 8 (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4137/32768 : ℝ)) (248038948009/250000000000 : ℝ) (496077896019/500000000000 : ℝ) (250221923281/500000000000 : ℝ) (125110961643/250000000000 : ℝ) (396155201761/500000000000 : ℝ) (39615520177/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0321_exp_lower
  have heNumeric : (2054900747829/1000000000000 : ℝ)/4 ≤ Real.exp (-4262827598281/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900747829/1000000000000 : ℝ)/4 ≤ Real.exp ((16547/131072 : ℝ)-(39615520177/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16547/131072 : ℝ) (4137/32768 : ℝ) (39615520177/50000000000 : ℝ) (2054900747829/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0322; no trusted numerical premise.
theorem cover8_leaf0322_exp_radius : (998029150147330093/1000000000000000000 : ℝ) ≤ Real.exp ((-16549/1048576 : ℝ)/8) ∧ Real.exp ((-16549/1048576 : ℝ)/8) ≤ (499014575073665047/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16549/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0322_exp_lower : (920113397169844601/1000000000000000000 : ℝ) ≤ Real.exp ((-5328534959447/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328534959447/8000000000000 : ℝ)/8) ≤ (460056698584922301/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328534959447/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0322_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450314631/500000000000 : ℝ) ≤ 4*Real.exp (4137/32768 : ℝ)*Real.exp (-mu (radius 8 (16549/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450314631/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16549/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0322_exp_radius
  have hrNumeric : (984341532513/1000000000000 : ℝ) ≤ Real.exp (-16549/1048576 : ℝ) ∧ Real.exp (-16549/1048576 : ℝ) ≤ (492170766257/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984341532513/1000000000000 : ℝ) ≤ (radius 8 (16549/131072 : ℝ)) ∧ (radius 8 (16549/131072 : ℝ)) ≤ (492170766257/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16549/131072 : ℝ)) (984341532513/1000000000000 : ℝ) (492170766257/500000000000 : ℝ) (35254359939/200000000000 : ℝ) (88135899851/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16549/131072 : ℝ)) (984341532513/1000000000000 : ℝ) (492170766257/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16549/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984341532513/1000000000000 : ℝ) (492170766257/500000000000 : ℝ) (62010672891/62500000000 : ℝ) (992170766257/1000000000000 : ℝ) (992139875477/1000000000000 : ℝ) (992139875479/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16549/131072 : ℝ)) 1 (62010672891/62500000000 : ℝ) (992170766257/1000000000000 : ℝ) (992139875477/1000000000000 : ℝ) (992139875479/1000000000000 : ℝ) (496077660433/500000000000 : ℝ) (248038830217/250000000000 : ℝ) (496077660373/500000000000 : ℝ) (248038830187/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16549/131072 : ℝ)) 2 (496077660433/500000000000 : ℝ) (248038830217/250000000000 : ℝ) (496077660373/500000000000 : ℝ) (248038830187/250000000000 : ℝ) (496077660403/500000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16549/131072 : ℝ)) 3 (496077660403/500000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16549/131072 : ℝ)) 4 (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16549/131072 : ℝ)) 5 (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16549/131072 : ℝ)) 6 (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16549/131072 : ℝ)) 7 (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16549/131072 : ℝ))) (35254359939/200000000000 : ℝ) (88135899851/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16549/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35254359939/200000000000 : ℝ) (88135899851/500000000000 : ℝ) (588135899847/1000000000000 : ℝ) (588135899851/1000000000000 : ℝ) (419847352849/1000000000000 : ℝ) (419847352859/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16549/131072 : ℝ))) 1 (588135899847/1000000000000 : ℝ) (588135899851/1000000000000 : ℝ) (419847352849/1000000000000 : ℝ) (419847352859/1000000000000 : ℝ) (125997906587/250000000000 : ℝ) (100798325271/200000000000 : ℝ) (496917800713/1000000000000 : ℝ) (248458900361/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16549/131072 : ℝ))) 2 (125997906587/250000000000 : ℝ) (100798325271/200000000000 : ℝ) (496917800713/1000000000000 : ℝ) (248458900361/500000000000 : ℝ) (50045471353/100000000000 : ℝ) (500454713539/1000000000000 : ℝ) (125110553747/250000000000 : ℝ) (500442214997/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16549/131072 : ℝ))) 3 (50045471353/100000000000 : ℝ) (500454713539/1000000000000 : ℝ) (125110553747/250000000000 : ℝ) (500442214997/1000000000000 : ℝ) (500448464259/1000000000000 : ℝ) (125112116067/250000000000 : ℝ) (500448464219/1000000000000 : ℝ) (500448464229/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16549/131072 : ℝ))) 4 (500448464259/1000000000000 : ℝ) (125112116067/250000000000 : ℝ) (500448464219/1000000000000 : ℝ) (500448464229/1000000000000 : ℝ) (500448464239/1000000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16549/131072 : ℝ))) 5 (500448464239/1000000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16549/131072 : ℝ))) 6 (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16549/131072 : ℝ))) 7 (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16549/131072 : ℝ)) hmem 8 (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16549/131072 : ℝ))) hcmem 8 (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16549/131072 : ℝ)) (198431064161/200000000000 : ℝ) (124019415101/125000000000 : ℝ) (250224232119/500000000000 : ℝ) (500448464249/1000000000000 : ℝ) (396159045307/500000000000 : ℝ) (396159045317/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0322_exp_lower
  have heNumeric : (1027450314631/500000000000 : ℝ)/4 ≤ Real.exp (-5328534959447/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450314631/500000000000 : ℝ)/4 ≤ Real.exp ((4137/32768 : ℝ)-(396159045317/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4137/32768 : ℝ) (16549/131072 : ℝ) (396159045317/500000000000 : ℝ) (1027450314631/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0323; no trusted numerical premise.
theorem cover8_leaf0323_exp_radius : (249507257793247811/250000000000000000 : ℝ) ≤ Real.exp ((-8275/524288 : ℝ)/8) ∧ Real.exp ((-8275/524288 : ℝ)/8) ≤ (199605806234598249/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8275/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0323_exp_lower : (28753543455342733/31250000000000000 : ℝ) ≤ Real.exp ((-21314141673771/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314141673771/32000000000000 : ℝ)/8) ≤ (920113390570967457/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314141673771/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0323_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900511363/1000000000000 : ℝ) ≤ 4*Real.exp (16549/131072 : ℝ)*Real.exp (-mu (radius 8 (8275/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900511363/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8275/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0323_exp_radius
  have hrNumeric : (984340593773/1000000000000 : ℝ) ≤ Real.exp (-8275/524288 : ℝ) ∧ Real.exp (-8275/524288 : ℝ) ≤ (492170296887/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984340593773/1000000000000 : ℝ) ≤ (radius 8 (8275/65536 : ℝ)) ∧ (radius 8 (8275/65536 : ℝ)) ≤ (492170296887/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8275/65536 : ℝ)) (984340593773/1000000000000 : ℝ) (492170296887/500000000000 : ℝ) (176277041751/1000000000000 : ℝ) (88138520879/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8275/65536 : ℝ)) (984340593773/1000000000000 : ℝ) (492170296887/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8275/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984340593773/1000000000000 : ℝ) (492170296887/500000000000 : ℝ) (496085148443/500000000000 : ℝ) (992170296887/1000000000000 : ℝ) (992139402389/1000000000000 : ℝ) (99213940239/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8275/65536 : ℝ)) 1 (496085148443/500000000000 : ℝ) (992170296887/1000000000000 : ℝ) (992139402389/1000000000000 : ℝ) (99213940239/100000000000 : ℝ) (992154849637/1000000000000 : ℝ) (992154849639/1000000000000 : ℝ) (992154849517/1000000000000 : ℝ) (992154849519/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8275/65536 : ℝ)) 2 (992154849637/1000000000000 : ℝ) (992154849639/1000000000000 : ℝ) (992154849517/1000000000000 : ℝ) (992154849519/1000000000000 : ℝ) (992154849577/1000000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8275/65536 : ℝ)) 3 (992154849577/1000000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8275/65536 : ℝ)) 4 (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8275/65536 : ℝ)) 5 (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8275/65536 : ℝ)) 6 (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8275/65536 : ℝ)) 7 (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8275/65536 : ℝ))) (176277041751/1000000000000 : ℝ) (88138520879/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8275/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176277041751/1000000000000 : ℝ) (88138520879/500000000000 : ℝ) (4705108167/8000000000 : ℝ) (588138520879/1000000000000 : ℝ) (83970719123/200000000000 : ℝ) (52481699453/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8275/65536 : ℝ))) 1 (4705108167/8000000000 : ℝ) (588138520879/1000000000000 : ℝ) (83970719123/200000000000 : ℝ) (52481699453/125000000000 : ℝ) (100799211649/200000000000 : ℝ) (125999014563/250000000000 : ℝ) (124230650583/250000000000 : ℝ) (24846130117/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8275/65536 : ℝ))) 2 (100799211649/200000000000 : ℝ) (125999014563/250000000000 : ℝ) (124230650583/250000000000 : ℝ) (24846130117/50000000000 : ℝ) (31278708143/62500000000 : ℝ) (62557416287/125000000000 : ℝ) (31277927073/62500000000 : ℝ) (62555854147/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8275/65536 : ℝ))) 3 (31278708143/62500000000 : ℝ) (62557416287/125000000000 : ℝ) (31277927073/62500000000 : ℝ) (62555854147/125000000000 : ℝ) (3909789701/7812500000 : ℝ) (62556635217/125000000000 : ℝ) (62556635211/125000000000 : ℝ) (500453081697/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8275/65536 : ℝ))) 4 (3909789701/7812500000 : ℝ) (62556635217/125000000000 : ℝ) (62556635211/125000000000 : ℝ) (500453081697/1000000000000 : ℝ) (125113270427/250000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8275/65536 : ℝ))) 5 (125113270427/250000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8275/65536 : ℝ))) 6 (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8275/65536 : ℝ))) 7 (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8275/65536 : ℝ)) hmem 8 (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8275/65536 : ℝ))) hcmem 8 (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8275/65536 : ℝ)) (124019356197/125000000000 : ℝ) (992154849579/1000000000000 : ℝ) (500453081707/1000000000000 : ℝ) (500453081717/1000000000000 : ℝ) (99040722173/125000000000 : ℝ) (792325777403/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0323_exp_lower
  have heNumeric : (2054900511363/1000000000000 : ℝ)/4 ≤ Real.exp (-21314141673771/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900511363/1000000000000 : ℝ)/4 ≤ Real.exp ((16549/131072 : ℝ)-(792325777403/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16549/131072 : ℝ) (8275/65536 : ℝ) (792325777403/1000000000000 : ℝ) (2054900511363/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0324; no trusted numerical premise.
theorem cover8_leaf0324_exp_radius : (499014456099333289/500000000000000000 : ℝ) ≤ Real.exp ((-16551/1048576 : ℝ)/8) ∧ Real.exp ((-16551/1048576 : ℝ)/8) ≤ (998028912198666579/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16551/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0324_exp_lower : (920113384007514723/1000000000000000000 : ℝ) ≤ Real.exp ((-10657071749949/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657071749949/16000000000000 : ℝ)/8) ≤ (230028346001878681/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657071749949/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0324_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054900394097/1000000000000 : ℝ) ≤ 4*Real.exp (8275/65536 : ℝ)*Real.exp (-mu (radius 8 (16551/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054900394097/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16551/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0324_exp_radius
  have hrNumeric : (984339655033/1000000000000 : ℝ) ≤ Real.exp (-16551/1048576 : ℝ) ∧ Real.exp (-16551/1048576 : ℝ) ≤ (492169827517/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984339655033/1000000000000 : ℝ) ≤ (radius 8 (16551/131072 : ℝ)) ∧ (radius 8 (16551/131072 : ℝ)) ≤ (492169827517/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16551/131072 : ℝ)) (984339655033/1000000000000 : ℝ) (492169827517/500000000000 : ℝ) (88141141823/500000000000 : ℝ) (44070570913/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16551/131072 : ℝ)) (984339655033/1000000000000 : ℝ) (492169827517/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16551/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984339655033/1000000000000 : ℝ) (492169827517/500000000000 : ℝ) (248042456879/250000000000 : ℝ) (992169827517/1000000000000 : ℝ) (9921389293/10000000000 : ℝ) (992138929301/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16551/131072 : ℝ)) 1 (248042456879/250000000000 : ℝ) (992169827517/1000000000000 : ℝ) (9921389293/10000000000 : ℝ) (992138929301/1000000000000 : ℝ) (124019297301/125000000000 : ℝ) (992154378409/1000000000000 : ℝ) (992154378287/1000000000000 : ℝ) (992154378289/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16551/131072 : ℝ)) 2 (124019297301/125000000000 : ℝ) (992154378409/1000000000000 : ℝ) (992154378287/1000000000000 : ℝ) (992154378289/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16551/131072 : ℝ)) 3 (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16551/131072 : ℝ)) 4 (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16551/131072 : ℝ)) 5 (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16551/131072 : ℝ)) 6 (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16551/131072 : ℝ)) 7 (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16551/131072 : ℝ))) (88141141823/500000000000 : ℝ) (44070570913/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16551/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88141141823/500000000000 : ℝ) (44070570913/250000000000 : ℝ) (588141141823/1000000000000 : ℝ) (294070570913/500000000000 : ℝ) (26241239881/62500000000 : ℝ) (52482479763/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16551/131072 : ℝ))) 1 (588141141823/1000000000000 : ℝ) (294070570913/500000000000 : ℝ) (26241239881/62500000000 : ℝ) (52482479763/125000000000 : ℝ) (504000489959/1000000000000 : ℝ) (100800097993/200000000000 : ℝ) (99385480747/200000000000 : ℝ) (248463701871/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16551/131072 : ℝ))) 2 (504000489959/1000000000000 : ℝ) (100800097993/200000000000 : ℝ) (99385480747/200000000000 : ℝ) (248463701871/500000000000 : ℝ) (500463946847/1000000000000 : ℝ) (250231973427/500000000000 : ℝ) (125112862787/250000000000 : ℝ) (100090290231/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16551/131072 : ℝ))) 3 (500463946847/1000000000000 : ℝ) (250231973427/500000000000 : ℝ) (125112862787/250000000000 : ℝ) (100090290231/200000000000 : ℝ) (500457698997/1000000000000 : ℝ) (100091539801/200000000000 : ℝ) (250228849479/500000000000 : ℝ) (250228849483/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16551/131072 : ℝ))) 4 (500457698997/1000000000000 : ℝ) (100091539801/200000000000 : ℝ) (250228849479/500000000000 : ℝ) (250228849483/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16551/131072 : ℝ))) 5 (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16551/131072 : ℝ))) 6 (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16551/131072 : ℝ))) 7 (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16551/131072 : ℝ)) hmem 8 (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16551/131072 : ℝ))) hcmem 8 (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16551/131072 : ℝ)) (992154378347/1000000000000 : ℝ) (992154378349/1000000000000 : ℝ) (500457698977/1000000000000 : ℝ) (250228849493/500000000000 : ℝ) (99041682981/125000000000 : ℝ) (99041682983/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0324_exp_lower
  have heNumeric : (2054900394097/1000000000000 : ℝ)/4 ≤ Real.exp (-10657071749949/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054900394097/1000000000000 : ℝ)/4 ≤ Real.exp ((8275/65536 : ℝ)-(99041682983/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8275/65536 : ℝ) (16551/131072 : ℝ) (99041682983/125000000000 : ℝ) (2054900394097/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0300_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0300_certificate
#check SmaleRate.Proofs.cover8_leaf0301_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0301_certificate
#check SmaleRate.Proofs.cover8_leaf0302_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0302_certificate
#check SmaleRate.Proofs.cover8_leaf0303_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0303_certificate
#check SmaleRate.Proofs.cover8_leaf0304_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0304_certificate
#check SmaleRate.Proofs.cover8_leaf0305_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0305_certificate
#check SmaleRate.Proofs.cover8_leaf0306_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0306_certificate
#check SmaleRate.Proofs.cover8_leaf0307_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0307_certificate
#check SmaleRate.Proofs.cover8_leaf0308_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0308_certificate
#check SmaleRate.Proofs.cover8_leaf0309_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0309_certificate
#check SmaleRate.Proofs.cover8_leaf0310_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0310_certificate
#check SmaleRate.Proofs.cover8_leaf0311_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0311_certificate
#check SmaleRate.Proofs.cover8_leaf0312_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0312_certificate
#check SmaleRate.Proofs.cover8_leaf0313_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0313_certificate
#check SmaleRate.Proofs.cover8_leaf0314_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0314_certificate
#check SmaleRate.Proofs.cover8_leaf0315_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0315_certificate
#check SmaleRate.Proofs.cover8_leaf0316_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0316_certificate
#check SmaleRate.Proofs.cover8_leaf0317_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0317_certificate
#check SmaleRate.Proofs.cover8_leaf0318_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0318_certificate
#check SmaleRate.Proofs.cover8_leaf0319_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0319_certificate
#check SmaleRate.Proofs.cover8_leaf0320_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0320_certificate
#check SmaleRate.Proofs.cover8_leaf0321_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0321_certificate
#check SmaleRate.Proofs.cover8_leaf0322_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0322_certificate
#check SmaleRate.Proofs.cover8_leaf0323_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0323_certificate
#check SmaleRate.Proofs.cover8_leaf0324_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0324_certificate
