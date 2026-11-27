/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0425; no trusted numerical premise.
theorem cover8_leaf0425_exp_radius : (499011362776663939/500000000000000000 : ℝ) ≤ Real.exp ((-16603/1048576 : ℝ)/8) ∧ Real.exp ((-16603/1048576 : ℝ)/8) ≤ (998022725553327879/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16603/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0425_exp_lower : (920113531333538673/1000000000000000000 : ℝ) ≤ Real.exp ((-42628205019771/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628205019771/64000000000000 : ℝ)/8) ≤ (460056765666769337/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628205019771/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0425_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054903026299/1000000000000 : ℝ) ≤ 4*Real.exp (33205/262144 : ℝ)*Real.exp (-mu (radius 8 (16603/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054903026299/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16603/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0425_exp_radius
  have hrNumeric : (15379544403/15625000000 : ℝ) ≤ Real.exp (-16603/1048576 : ℝ) ∧ Real.exp (-16603/1048576 : ℝ) ≤ (984290841793/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (15379544403/15625000000 : ℝ) ≤ (radius 8 (16603/131072 : ℝ)) ∧ (radius 8 (16603/131072 : ℝ)) ≤ (984290841793/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16603/131072 : ℝ)) (15379544403/15625000000 : ℝ) (984290841793/1000000000000 : ℝ) (17655463393/100000000000 : ℝ) (176554633937/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16603/131072 : ℝ)) (15379544403/15625000000 : ℝ) (984290841793/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16603/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (15379544403/15625000000 : ℝ) (984290841793/1000000000000 : ℝ) (31004544403/31250000000 : ℝ) (992145420897/1000000000000 : ℝ) (31003572781/31250000000 : ℝ) (992114328993/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16603/131072 : ℝ)) 1 (31004544403/31250000000 : ℝ) (992145420897/1000000000000 : ℝ) (31003572781/31250000000 : ℝ) (992114328993/1000000000000 : ℝ) (968876831/976562500 : ℝ) (198425974989/200000000000 : ℝ) (496064937411/500000000000 : ℝ) (124016234353/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16603/131072 : ℝ)) 2 (968876831/976562500 : ℝ) (198425974989/200000000000 : ℝ) (496064937411/500000000000 : ℝ) (124016234353/125000000000 : ℝ) (992129874883/1000000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16603/131072 : ℝ)) 3 (992129874883/1000000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16603/131072 : ℝ)) 4 (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16603/131072 : ℝ)) 5 (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16603/131072 : ℝ)) 6 (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16603/131072 : ℝ)) 7 (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16603/131072 : ℝ))) (17655463393/100000000000 : ℝ) (176554633937/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16603/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17655463393/100000000000 : ℝ) (176554633937/1000000000000 : ℝ) (117655463393/200000000000 : ℝ) (588277316969/1000000000000 : ℝ) (210092023843/500000000000 : ℝ) (84036809539/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16603/131072 : ℝ))) 1 (117655463393/200000000000 : ℝ) (588277316969/1000000000000 : ℝ) (210092023843/500000000000 : ℝ) (84036809539/200000000000 : ℝ) (20169227293/40000000000 : ℝ) (126057670583/250000000000 : ℝ) (124294193399/250000000000 : ℝ) (124294193401/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16603/131072 : ℝ))) 2 (20169227293/40000000000 : ℝ) (126057670583/250000000000 : ℝ) (124294193399/250000000000 : ℝ) (124294193401/250000000000 : ℝ) (12517593199/25000000000 : ℝ) (15646991499/31250000000 : ℝ) (250345652941/500000000000 : ℝ) (500691305891/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16603/131072 : ℝ))) 3 (12517593199/25000000000 : ℝ) (15646991499/31250000000 : ℝ) (250345652941/500000000000 : ℝ) (500691305891/1000000000000 : ℝ) (500697516921/1000000000000 : ℝ) (50069751693/100000000000 : ℝ) (250348758441/500000000000 : ℝ) (500697516891/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16603/131072 : ℝ))) 4 (500697516921/1000000000000 : ℝ) (50069751693/100000000000 : ℝ) (250348758441/500000000000 : ℝ) (500697516891/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16603/131072 : ℝ))) 5 (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16603/131072 : ℝ))) 6 (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16603/131072 : ℝ))) 7 (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16603/131072 : ℝ)) hmem 8 (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16603/131072 : ℝ))) hcmem 8 (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16603/131072 : ℝ)) (496064937441/500000000000 : ℝ) (198425974977/200000000000 : ℝ) (500697516901/1000000000000 : ℝ) (500697516911/1000000000000 : ℝ) (19818318153/25000000000 : ℝ) (792732726139/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0425_exp_lower
  have heNumeric : (2054903026299/1000000000000 : ℝ)/4 ≤ Real.exp (-42628205019771/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054903026299/1000000000000 : ℝ)/4 ≤ Real.exp ((33205/262144 : ℝ)-(792732726139/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33205/262144 : ℝ) (16603/131072 : ℝ) (792732726139/1000000000000 : ℝ) (2054903026299/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0426; no trusted numerical premise.
theorem cover8_leaf0426_exp_radius : (31188208314579363/31250000000000000 : ℝ) ≤ Real.exp ((-33207/2097152 : ℝ)/8) ∧ Real.exp ((-33207/2097152 : ℝ)/8) ≤ (998022666066539617/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33207/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0426_exp_lower : (230028382251247977/250000000000000000 : ℝ) ≤ Real.exp ((-21314103157749/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314103157749/32000000000000 : ℝ)/8) ≤ (920113529004991909/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314103157749/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0426_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862873087/125000000000 : ℝ) ≤ 4*Real.exp (16603/131072 : ℝ)*Real.exp (-mu (radius 8 (33207/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862873087/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33207/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0426_exp_radius
  have hrNumeric : (196858074489/200000000000 : ℝ) ≤ Real.exp (-33207/2097152 : ℝ) ∧ Real.exp (-33207/2097152 : ℝ) ≤ (492145186223/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196858074489/200000000000 : ℝ) ≤ (radius 8 (33207/262144 : ℝ)) ∧ (radius 8 (33207/262144 : ℝ)) ≤ (492145186223/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33207/262144 : ℝ)) (196858074489/200000000000 : ℝ) (492145186223/500000000000 : ℝ) (44139312629/250000000000 : ℝ) (176557250523/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33207/262144 : ℝ)) (196858074489/200000000000 : ℝ) (492145186223/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33207/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196858074489/200000000000 : ℝ) (492145186223/500000000000 : ℝ) (496072593111/500000000000 : ℝ) (992145186223/1000000000000 : ℝ) (992114092453/1000000000000 : ℝ) (198422818491/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33207/262144 : ℝ)) 1 (496072593111/500000000000 : ℝ) (992145186223/1000000000000 : ℝ) (992114092453/1000000000000 : ℝ) (198422818491/200000000000 : ℝ) (992129639337/1000000000000 : ℝ) (992129639339/1000000000000 : ℝ) (198425927843/200000000000 : ℝ) (496064819609/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33207/262144 : ℝ)) 2 (992129639337/1000000000000 : ℝ) (992129639339/1000000000000 : ℝ) (198425927843/200000000000 : ℝ) (496064819609/500000000000 : ℝ) (248032409819/250000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33207/262144 : ℝ)) 3 (248032409819/250000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33207/262144 : ℝ)) 4 (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33207/262144 : ℝ)) 5 (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33207/262144 : ℝ)) 6 (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33207/262144 : ℝ)) 7 (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33207/262144 : ℝ))) (44139312629/250000000000 : ℝ) (176557250523/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33207/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44139312629/250000000000 : ℝ) (176557250523/1000000000000 : ℝ) (294139312629/500000000000 : ℝ) (294139312631/500000000000 : ℝ) (420187161293/1000000000000 : ℝ) (210093580651/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33207/262144 : ℝ))) 1 (294139312629/500000000000 : ℝ) (294139312631/500000000000 : ℝ) (420187161293/1000000000000 : ℝ) (210093580651/500000000000 : ℝ) (20169315731/40000000000 : ℝ) (252116446641/500000000000 : ℝ) (248589584253/500000000000 : ℝ) (248589584257/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33207/262144 : ℝ))) 2 (20169315731/40000000000 : ℝ) (252116446641/500000000000 : ℝ) (248589584253/500000000000 : ℝ) (248589584257/500000000000 : ℝ) (50070603089/100000000000 : ℝ) (250353015449/500000000000 : ℝ) (500693609517/1000000000000 : ℝ) (250346804763/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33207/262144 : ℝ))) 3 (50070603089/100000000000 : ℝ) (250353015449/500000000000 : ℝ) (500693609517/1000000000000 : ℝ) (250346804763/500000000000 : ℝ) (500699820203/1000000000000 : ℝ) (125174955053/250000000000 : ℝ) (125174955041/250000000000 : ℝ) (250349910087/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33207/262144 : ℝ))) 4 (500699820203/1000000000000 : ℝ) (125174955053/250000000000 : ℝ) (125174955041/250000000000 : ℝ) (250349910087/500000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33207/262144 : ℝ))) 5 (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33207/262144 : ℝ))) 6 (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33207/262144 : ℝ))) 7 (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33207/262144 : ℝ)) hmem 8 (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33207/262144 : ℝ))) hcmem 8 (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33207/262144 : ℝ)) (39685185571/40000000000 : ℝ) (992129639279/1000000000000 : ℝ) (500699820183/1000000000000 : ℝ) (500699820193/1000000000000 : ℝ) (396368280531/500000000000 : ℝ) (396368280541/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0426_exp_lower
  have heNumeric : (256862873087/125000000000 : ℝ)/4 ≤ Real.exp (-21314103157749/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862873087/125000000000 : ℝ)/4 ≤ Real.exp ((16603/131072 : ℝ)-(396368280541/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16603/131072 : ℝ) (33207/262144 : ℝ) (396368280541/500000000000 : ℝ) (256862873087/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0427; no trusted numerical premise.
theorem cover8_leaf0427_exp_radius : (9980226065797549/10000000000000000 : ℝ) ≤ Real.exp ((-4151/262144 : ℝ)/8) ∧ Real.exp ((-4151/262144 : ℝ)/8) ≤ (998022606579754901/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4151/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0427_exp_lower : (46005676334305317/50000000000000000 : ℝ) ≤ Real.exp ((-42628207605849/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628207605849/64000000000000 : ℝ)/8) ≤ (920113526686106341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628207605849/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0427_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980588653/200000000000 : ℝ) ≤ 4*Real.exp (33207/262144 : ℝ)*Real.exp (-mu (radius 8 (4151/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (410980588653/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4151/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0427_exp_radius
  have hrNumeric : (984289903099/1000000000000 : ℝ) ≤ Real.exp (-4151/262144 : ℝ) ∧ Real.exp (-4151/262144 : ℝ) ≤ (9842899031/10000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984289903099/1000000000000 : ℝ) ≤ (radius 8 (4151/32768 : ℝ)) ∧ (radius 8 (4151/32768 : ℝ)) ≤ (9842899031/10000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4151/32768 : ℝ)) (984289903099/1000000000000 : ℝ) (9842899031/10000000000 : ℝ) (176559867057/1000000000000 : ℝ) (22069983383/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4151/32768 : ℝ)) (984289903099/1000000000000 : ℝ) (9842899031/10000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4151/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984289903099/1000000000000 : ℝ) (9842899031/10000000000 : ℝ) (992144951549/1000000000000 : ℝ) (19842899031/20000000000 : ℝ) (198422771183/200000000000 : ℝ) (248028463979/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4151/32768 : ℝ)) 1 (992144951549/1000000000000 : ℝ) (19842899031/20000000000 : ℝ) (198422771183/200000000000 : ℝ) (248028463979/250000000000 : ℝ) (248032350933/250000000000 : ℝ) (992129403733/1000000000000 : ℝ) (99212940361/100000000000 : ℝ) (248032350903/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4151/32768 : ℝ)) 2 (248032350933/250000000000 : ℝ) (992129403733/1000000000000 : ℝ) (99212940361/100000000000 : ℝ) (248032350903/250000000000 : ℝ) (992129403671/1000000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4151/32768 : ℝ)) 3 (992129403671/1000000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4151/32768 : ℝ)) 4 (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4151/32768 : ℝ)) 5 (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4151/32768 : ℝ)) 6 (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4151/32768 : ℝ)) 7 (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4151/32768 : ℝ))) (176559867057/1000000000000 : ℝ) (22069983383/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4151/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176559867057/1000000000000 : ℝ) (22069983383/125000000000 : ℝ) (73534991691/125000000000 : ℝ) (147069983383/250000000000 : ℝ) (52523784353/125000000000 : ℝ) (420190274833/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4151/32768 : ℝ))) 1 (73534991691/125000000000 : ℝ) (147069983383/250000000000 : ℝ) (52523784353/125000000000 : ℝ) (420190274833/1000000000000 : ℝ) (31514694011/62500000000 : ℝ) (504235104183/1000000000000 : ℝ) (497181563357/1000000000000 : ℝ) (99436312673/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4151/32768 : ℝ))) 2 (31514694011/62500000000 : ℝ) (504235104183/1000000000000 : ℝ) (497181563357/1000000000000 : ℝ) (99436312673/200000000000 : ℝ) (250354166883/500000000000 : ℝ) (250354166887/500000000000 : ℝ) (250347956549/500000000000 : ℝ) (500695913107/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4151/32768 : ℝ))) 3 (250354166883/500000000000 : ℝ) (250354166887/500000000000 : ℝ) (250347956549/500000000000 : ℝ) (500695913107/1000000000000 : ℝ) (62587765429/125000000000 : ℝ) (500702123441/1000000000000 : ℝ) (500702123393/1000000000000 : ℝ) (250351061701/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4151/32768 : ℝ))) 4 (62587765429/125000000000 : ℝ) (500702123441/1000000000000 : ℝ) (500702123393/1000000000000 : ℝ) (250351061701/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4151/32768 : ℝ))) 5 (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4151/32768 : ℝ))) 6 (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4151/32768 : ℝ))) 7 (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4151/32768 : ℝ)) hmem 8 (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4151/32768 : ℝ))) hcmem 8 (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4151/32768 : ℝ)) (99212940367/100000000000 : ℝ) (992129403673/1000000000000 : ℝ) (125175530853/250000000000 : ℝ) (250351061711/500000000000 : ℝ) (396370197961/500000000000 : ℝ) (792740395941/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0427_exp_lower
  have heNumeric : (410980588653/200000000000 : ℝ)/4 ≤ Real.exp (-42628207605849/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980588653/200000000000 : ℝ)/4 ≤ Real.exp ((33207/262144 : ℝ)-(792740395941/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33207/262144 : ℝ) (4151/32768 : ℝ) (792740395941/1000000000000 : ℝ) (410980588653/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0428; no trusted numerical premise.
theorem cover8_leaf0428_exp_radius : (99802254709297373/100000000000000000 : ℝ) ≤ Real.exp ((-33209/2097152 : ℝ)/8) ∧ Real.exp ((-33209/2097152 : ℝ)/8) ≤ (998022547092973731/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33209/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0428_exp_lower : (230028381094047971/250000000000000000 : ℝ) ≤ Real.exp ((-5328526111401/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328526111401/8000000000000 : ℝ)/8) ≤ (184022704875238377/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328526111401/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0428_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980580399/200000000000 : ℝ) ≤ 4*Real.exp (4151/32768 : ℝ)*Real.exp (-mu (radius 8 (33209/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980580399/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33209/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0428_exp_radius
  have hrNumeric : (984289433753/1000000000000 : ℝ) ≤ Real.exp (-33209/2097152 : ℝ) ∧ Real.exp (-33209/2097152 : ℝ) ≤ (492144716877/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984289433753/1000000000000 : ℝ) ≤ (radius 8 (33209/262144 : ℝ)) ∧ (radius 8 (33209/262144 : ℝ)) ≤ (492144716877/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33209/262144 : ℝ)) (984289433753/1000000000000 : ℝ) (492144716877/500000000000 : ℝ) (88281241779/500000000000 : ℝ) (44140620891/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33209/262144 : ℝ)) (984289433753/1000000000000 : ℝ) (492144716877/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33209/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984289433753/1000000000000 : ℝ) (492144716877/500000000000 : ℝ) (248036179219/250000000000 : ℝ) (992144716877/1000000000000 : ℝ) (62007101211/62500000000 : ℝ) (496056809689/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33209/262144 : ℝ)) 1 (248036179219/250000000000 : ℝ) (992144716877/1000000000000 : ℝ) (62007101211/62500000000 : ℝ) (496056809689/500000000000 : ℝ) (496064584063/500000000000 : ℝ) (3875504563/3906250000 : ℝ) (248032292001/250000000000 : ℝ) (496064584003/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33209/262144 : ℝ)) 2 (496064584063/500000000000 : ℝ) (3875504563/3906250000 : ℝ) (248032292001/250000000000 : ℝ) (496064584003/500000000000 : ℝ) (198425833613/200000000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33209/262144 : ℝ)) 3 (198425833613/200000000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33209/262144 : ℝ)) 4 (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33209/262144 : ℝ)) 5 (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33209/262144 : ℝ)) 6 (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33209/262144 : ℝ)) 7 (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33209/262144 : ℝ))) (88281241779/500000000000 : ℝ) (44140620891/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33209/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88281241779/500000000000 : ℝ) (44140620891/250000000000 : ℝ) (588281241779/1000000000000 : ℝ) (294140620891/500000000000 : ℝ) (105048347071/250000000000 : ℝ) (105048347073/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33209/262144 : ℝ))) 1 (588281241779/1000000000000 : ℝ) (294140620891/500000000000 : ℝ) (105048347071/250000000000 : ℝ) (105048347073/250000000000 : ℝ) (504237315031/1000000000000 : ℝ) (504237315037/1000000000000 : ℝ) (99436791631/200000000000 : ℝ) (248591979081/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33209/262144 : ℝ))) 2 (504237315031/1000000000000 : ℝ) (504237315037/1000000000000 : ℝ) (99436791631/200000000000 : ℝ) (248591979081/500000000000 : ℝ) (500710636593/1000000000000 : ℝ) (2503553183/5000000000 : ℝ) (50069821663/100000000000 : ℝ) (500698216637/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33209/262144 : ℝ))) 3 (500710636593/1000000000000 : ℝ) (2503553183/5000000000 : ℝ) (50069821663/100000000000 : ℝ) (500698216637/1000000000000 : ℝ) (500704426611/1000000000000 : ℝ) (500704426619/1000000000000 : ℝ) (125176106643/250000000000 : ℝ) (25035221329/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33209/262144 : ℝ))) 4 (500704426611/1000000000000 : ℝ) (500704426619/1000000000000 : ℝ) (125176106643/250000000000 : ℝ) (25035221329/50000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33209/262144 : ℝ))) 5 (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33209/262144 : ℝ))) 6 (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33209/262144 : ℝ))) 7 (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33209/262144 : ℝ)) hmem 8 (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33209/262144 : ℝ))) hcmem 8 (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33209/262144 : ℝ)) (15502018251/15625000000 : ℝ) (992129168067/1000000000000 : ℝ) (500704426591/1000000000000 : ℝ) (2503522133/5000000000 : ℝ) (49546514419/62500000000 : ℝ) (396372115361/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0428_exp_lower
  have heNumeric : (410980580399/200000000000 : ℝ)/4 ≤ Real.exp (-5328526111401/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980580399/200000000000 : ℝ)/4 ≤ Real.exp ((4151/32768 : ℝ)-(396372115361/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4151/32768 : ℝ) (33209/262144 : ℝ) (396372115361/500000000000 : ℝ) (410980580399/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0429; no trusted numerical premise.
theorem cover8_leaf0429_exp_radius : (499011243803098053/500000000000000000 : ℝ) ≤ Real.exp ((-16605/1048576 : ℝ)/8) ∧ Real.exp ((-16605/1048576 : ℝ)/8) ≤ (998022487606196107/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16605/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0429_exp_lower : (920113522076053641/1000000000000000000 : ℝ) ≤ Real.exp ((-42628210171127/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628210171127/64000000000000 : ℝ)/8) ≤ (460056761038026821/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628210171127/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0429_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (20549028609/10000000000 : ℝ) ≤ 4*Real.exp (33209/262144 : ℝ)*Real.exp (-mu (radius 8 (16605/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (20549028609/10000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16605/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0429_exp_radius
  have hrNumeric : (123036120551/125000000000 : ℝ) ≤ Real.exp (-16605/1048576 : ℝ) ∧ Real.exp (-16605/1048576 : ℝ) ≤ (984288964409/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123036120551/125000000000 : ℝ) ≤ (radius 8 (16605/131072 : ℝ)) ∧ (radius 8 (16605/131072 : ℝ)) ≤ (984288964409/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16605/131072 : ℝ)) (123036120551/125000000000 : ℝ) (984288964409/1000000000000 : ℝ) (176565100013/1000000000000 : ℝ) (176565100019/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16605/131072 : ℝ)) (123036120551/125000000000 : ℝ) (984288964409/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16605/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123036120551/125000000000 : ℝ) (984288964409/1000000000000 : ℝ) (248036120551/250000000000 : ℝ) (198428896441/200000000000 : ℝ) (496056691419/500000000000 : ℝ) (24802834571/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16605/131072 : ℝ)) 1 (248036120551/250000000000 : ℝ) (198428896441/200000000000 : ℝ) (496056691419/500000000000 : ℝ) (24802834571/25000000000 : ℝ) (992128932521/1000000000000 : ℝ) (992128932523/1000000000000 : ℝ) (992128932399/1000000000000 : ℝ) (992128932401/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16605/131072 : ℝ)) 2 (992128932521/1000000000000 : ℝ) (992128932523/1000000000000 : ℝ) (992128932399/1000000000000 : ℝ) (992128932401/1000000000000 : ℝ) (49606446623/50000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16605/131072 : ℝ)) 3 (49606446623/50000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16605/131072 : ℝ)) 4 (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16605/131072 : ℝ)) 5 (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16605/131072 : ℝ)) 6 (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16605/131072 : ℝ)) 7 (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16605/131072 : ℝ))) (176565100013/1000000000000 : ℝ) (176565100019/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16605/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176565100013/1000000000000 : ℝ) (176565100019/1000000000000 : ℝ) (294141275003/500000000000 : ℝ) (58828255001/100000000000 : ℝ) (210098250833/500000000000 : ℝ) (210098250837/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16605/131072 : ℝ))) 1 (294141275003/500000000000 : ℝ) (58828255001/100000000000 : ℝ) (210098250833/500000000000 : ℝ) (210098250837/500000000000 : ℝ) (126059881459/250000000000 : ℝ) (252119762921/500000000000 : ℝ) (497186352893/1000000000000 : ℝ) (497186352901/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16605/131072 : ℝ))) 2 (126059881459/250000000000 : ℝ) (252119762921/500000000000 : ℝ) (497186352893/1000000000000 : ℝ) (497186352901/1000000000000 : ℝ) (125178234841/250000000000 : ℝ) (125178234843/250000000000 : ℝ) (250350260053/500000000000 : ℝ) (250350260057/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16605/131072 : ℝ))) 3 (125178234841/250000000000 : ℝ) (125178234843/250000000000 : ℝ) (250350260053/500000000000 : ℝ) (250350260057/500000000000 : ℝ) (100141345947/200000000000 : ℝ) (500706729743/1000000000000 : ℝ) (15647085303/31250000000 : ℝ) (100141345941/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16605/131072 : ℝ))) 4 (100141345947/200000000000 : ℝ) (500706729743/1000000000000 : ℝ) (15647085303/31250000000 : ℝ) (100141345941/200000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16605/131072 : ℝ))) 5 (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16605/131072 : ℝ))) 6 (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16605/131072 : ℝ))) 7 (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16605/131072 : ℝ)) hmem 8 (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16605/131072 : ℝ))) hcmem 8 (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16605/131072 : ℝ)) (992128932459/1000000000000 : ℝ) (496064466231/500000000000 : ℝ) (100141345943/200000000000 : ℝ) (125176682431/250000000000 : ℝ) (792748065401/1000000000000 : ℝ) (396374032709/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0429_exp_lower
  have heNumeric : (20549028609/10000000000 : ℝ)/4 ≤ Real.exp (-42628210171127/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (20549028609/10000000000 : ℝ)/4 ≤ Real.exp ((33209/262144 : ℝ)-(396374032709/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33209/262144 : ℝ) (16605/131072 : ℝ) (396374032709/500000000000 : ℝ) (20549028609/10000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0430; no trusted numerical premise.
theorem cover8_leaf0430_exp_radius : (998022428119422027/1000000000000000000 : ℝ) ≤ Real.exp ((-33211/2097152 : ℝ)/8) ∧ Real.exp ((-33211/2097152 : ℝ)/8) ≤ (249505607029855507/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33211/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0430_exp_lower : (46005675989175317/50000000000000000 : ℝ) ≤ Real.exp ((-21314105723411/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314105723411/32000000000000 : ℝ)/8) ≤ (920113519783506341/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314105723411/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0430_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745140997/50000000000 : ℝ) ≤ 4*Real.exp (16605/131072 : ℝ)*Real.exp (-mu (radius 8 (33211/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (102745140997/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33211/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0430_exp_radius
  have hrNumeric : (492144247531/500000000000 : ℝ) ≤ Real.exp (-33211/2097152 : ℝ) ∧ Real.exp (-33211/2097152 : ℝ) ≤ (984288495063/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492144247531/500000000000 : ℝ) ≤ (radius 8 (33211/262144 : ℝ)) ∧ (radius 8 (33211/262144 : ℝ)) ≤ (984288495063/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33211/262144 : ℝ)) (492144247531/500000000000 : ℝ) (984288495063/1000000000000 : ℝ) (176567716433/1000000000000 : ℝ) (4414192911/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33211/262144 : ℝ)) (492144247531/500000000000 : ℝ) (984288495063/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33211/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492144247531/500000000000 : ℝ) (984288495063/1000000000000 : ℝ) (992144247531/1000000000000 : ℝ) (248036061883/250000000000 : ℝ) (9921131463/10000000000 : ℝ) (992113146301/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33211/262144 : ℝ)) 1 (992144247531/1000000000000 : ℝ) (248036061883/250000000000 : ℝ) (9921131463/10000000000 : ℝ) (992113146301/1000000000000 : ℝ) (198425739383/200000000000 : ℝ) (992128696917/1000000000000 : ℝ) (992128696793/1000000000000 : ℝ) (198425739359/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33211/262144 : ℝ)) 2 (198425739383/200000000000 : ℝ) (992128696917/1000000000000 : ℝ) (992128696793/1000000000000 : ℝ) (198425739359/200000000000 : ℝ) (496064348427/500000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33211/262144 : ℝ)) 3 (496064348427/500000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33211/262144 : ℝ)) 4 (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33211/262144 : ℝ)) 5 (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33211/262144 : ℝ)) 6 (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33211/262144 : ℝ)) 7 (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33211/262144 : ℝ))) (176567716433/1000000000000 : ℝ) (4414192911/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33211/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176567716433/1000000000000 : ℝ) (4414192911/25000000000 : ℝ) (73535482277/125000000000 : ℝ) (29414192911/50000000000 : ℝ) (52524951873/125000000000 : ℝ) (420199614993/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33211/262144 : ℝ))) 1 (73535482277/125000000000 : ℝ) (29414192911/50000000000 : ℝ) (52524951873/125000000000 : ℝ) (420199614993/1000000000000 : ℝ) (2521208683/5000000000 : ℝ) (504241736607/1000000000000 : ℝ) (497188747583/1000000000000 : ℝ) (497188747591/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33211/262144 : ℝ))) 2 (2521208683/5000000000 : ℝ) (504241736607/1000000000000 : ℝ) (497188747583/1000000000000 : ℝ) (497188747591/1000000000000 : ℝ) (500715242091/1000000000000 : ℝ) (500715242099/1000000000000 : ℝ) (250351411769/500000000000 : ℝ) (250351411773/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33211/262144 : ℝ))) 3 (500715242091/1000000000000 : ℝ) (500715242099/1000000000000 : ℝ) (250351411769/500000000000 : ℝ) (250351411773/500000000000 : ℝ) (250354516407/500000000000 : ℝ) (500709032823/1000000000000 : ℝ) (20028361311/40000000000 : ℝ) (31294314549/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33211/262144 : ℝ))) 4 (250354516407/500000000000 : ℝ) (500709032823/1000000000000 : ℝ) (20028361311/40000000000 : ℝ) (31294314549/62500000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33211/262144 : ℝ))) 5 (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33211/262144 : ℝ))) 6 (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33211/262144 : ℝ))) 7 (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33211/262144 : ℝ)) hmem 8 (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33211/262144 : ℝ))) hcmem 8 (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33211/262144 : ℝ)) (992128696853/1000000000000 : ℝ) (124016087107/125000000000 : ℝ) (250354516397/500000000000 : ℝ) (125177258201/250000000000 : ℝ) (198187975007/250000000000 : ℝ) (49546993753/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0430_exp_lower
  have heNumeric : (102745140997/50000000000 : ℝ)/4 ≤ Real.exp (-21314105723411/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745140997/50000000000 : ℝ)/4 ≤ Real.exp ((16605/131072 : ℝ)-(49546993753/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16605/131072 : ℝ) (33211/262144 : ℝ) (49546993753/62500000000 : ℝ) (102745140997/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0431; no trusted numerical premise.
theorem cover8_leaf0431_exp_radius : (499011184316325747/500000000000000000 : ℝ) ≤ Real.exp ((-8303/524288 : ℝ)/8) ∧ Real.exp ((-8303/524288 : ℝ)/8) ≤ (199604473726530299/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8303/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0431_exp_lower : (5750709484381033/6250000000000000 : ℝ) ≤ Real.exp ((-42628212716949/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628212716949/64000000000000 : ℝ)/8) ≤ (920113517500965281/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628212716949/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0431_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902779159/1000000000000 : ℝ) ≤ 4*Real.exp (33211/262144 : ℝ)*Real.exp (-mu (radius 8 (8303/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902779159/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8303/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0431_exp_radius
  have hrNumeric : (984288025717/1000000000000 : ℝ) ≤ Real.exp (-8303/524288 : ℝ) ∧ Real.exp (-8303/524288 : ℝ) ≤ (492144012859/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984288025717/1000000000000 : ℝ) ≤ (radius 8 (8303/65536 : ℝ)) ∧ (radius 8 (8303/65536 : ℝ)) ≤ (492144012859/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8303/65536 : ℝ)) (984288025717/1000000000000 : ℝ) (492144012859/500000000000 : ℝ) (22071291601/125000000000 : ℝ) (35314066563/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8303/65536 : ℝ)) (984288025717/1000000000000 : ℝ) (492144012859/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8303/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984288025717/1000000000000 : ℝ) (492144012859/500000000000 : ℝ) (496072006429/500000000000 : ℝ) (992144012859/1000000000000 : ℝ) (496056454881/500000000000 : ℝ) (992112909763/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8303/65536 : ℝ)) 1 (496072006429/500000000000 : ℝ) (992144012859/1000000000000 : ℝ) (496056454881/500000000000 : ℝ) (992112909763/1000000000000 : ℝ) (99212846131/100000000000 : ℝ) (992128461311/1000000000000 : ℝ) (248032115297/250000000000 : ℝ) (99212846119/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8303/65536 : ℝ)) 2 (99212846131/100000000000 : ℝ) (992128461311/1000000000000 : ℝ) (248032115297/250000000000 : ℝ) (99212846119/100000000000 : ℝ) (992128461249/1000000000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8303/65536 : ℝ)) 3 (992128461249/1000000000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8303/65536 : ℝ)) 4 (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8303/65536 : ℝ)) 5 (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8303/65536 : ℝ)) 6 (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8303/65536 : ℝ)) 7 (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8303/65536 : ℝ))) (22071291601/125000000000 : ℝ) (35314066563/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8303/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22071291601/125000000000 : ℝ) (35314066563/200000000000 : ℝ) (147071291601/250000000000 : ℝ) (73535645801/125000000000 : ℝ) (16808109129/40000000000 : ℝ) (210101364117/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8303/65536 : ℝ))) 1 (147071291601/250000000000 : ℝ) (73535645801/125000000000 : ℝ) (16808109129/40000000000 : ℝ) (210101364117/500000000000 : ℝ) (252121973657/500000000000 : ℝ) (504243947321/1000000000000 : ℝ) (99438228443/200000000000 : ℝ) (497191142223/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8303/65536 : ℝ))) 2 (252121973657/500000000000 : ℝ) (504243947321/1000000000000 : ℝ) (99438228443/200000000000 : ℝ) (497191142223/1000000000000 : ℝ) (125179386191/250000000000 : ℝ) (125179386193/250000000000 : ℝ) (125176281729/250000000000 : ℝ) (125176281731/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8303/65536 : ℝ))) 3 (125179386191/250000000000 : ℝ) (125179386193/250000000000 : ℝ) (125176281729/250000000000 : ℝ) (125176281731/250000000000 : ℝ) (3129445849/6250000000 : ℝ) (62588916981/125000000000 : ℝ) (500711335801/1000000000000 : ℝ) (50071133581/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8303/65536 : ℝ))) 4 (3129445849/6250000000 : ℝ) (62588916981/125000000000 : ℝ) (500711335801/1000000000000 : ℝ) (50071133581/100000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8303/65536 : ℝ))) 5 (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8303/65536 : ℝ))) 6 (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8303/65536 : ℝ))) 7 (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8303/65536 : ℝ)) hmem 8 (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8303/65536 : ℝ))) hcmem 8 (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8303/65536 : ℝ)) (15502007207/15625000000 : ℝ) (992128461251/1000000000000 : ℝ) (25035566791/50000000000 : ℝ) (500711335829/1000000000000 : ℝ) (792755734573/1000000000000 : ℝ) (792755734591/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0431_exp_lower
  have heNumeric : (2054902779159/1000000000000 : ℝ)/4 ≤ Real.exp (-42628212716949/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902779159/1000000000000 : ℝ)/4 ≤ Real.exp ((33211/262144 : ℝ)-(792755734591/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33211/262144 : ℝ) (8303/65536 : ℝ) (792755734591/1000000000000 : ℝ) (2054902779159/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0432; no trusted numerical premise.
theorem cover8_leaf0432_exp_radius : (998022309145884507/1000000000000000000 : ℝ) ≤ Real.exp ((-33213/2097152 : ℝ)/8) ∧ Real.exp ((-33213/2097152 : ℝ)/8) ≤ (249505577286471127/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33213/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0432_exp_lower : (920113515227165303/1000000000000000000 : ℝ) ≤ Real.exp ((-10657053495553/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657053495553/16000000000000 : ℝ)/8) ≤ (115014189403395663/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657053495553/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0432_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451369267/500000000000 : ℝ) ≤ 4*Real.exp (8303/65536 : ℝ)*Real.exp (-mu (radius 8 (33213/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451369267/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33213/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0432_exp_radius
  have hrNumeric : (246071889093/250000000000 : ℝ) ≤ Real.exp (-33213/2097152 : ℝ) ∧ Real.exp (-33213/2097152 : ℝ) ≤ (984287556373/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246071889093/250000000000 : ℝ) ≤ (radius 8 (33213/262144 : ℝ)) ∧ (radius 8 (33213/262144 : ℝ)) ≤ (984287556373/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33213/262144 : ℝ)) (246071889093/250000000000 : ℝ) (984287556373/1000000000000 : ℝ) (176572949143/1000000000000 : ℝ) (3531458983/20000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33213/262144 : ℝ)) (246071889093/250000000000 : ℝ) (984287556373/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33213/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246071889093/250000000000 : ℝ) (984287556373/1000000000000 : ℝ) (496071889093/500000000000 : ℝ) (992143778187/1000000000000 : ℝ) (124014084153/125000000000 : ℝ) (39684506929/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33213/262144 : ℝ)) 1 (496071889093/500000000000 : ℝ) (992143778187/1000000000000 : ℝ) (124014084153/125000000000 : ℝ) (39684506929/40000000000 : ℝ) (198425645141/200000000000 : ℝ) (496064112853/500000000000 : ℝ) (992128225583/1000000000000 : ℝ) (198425645117/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33213/262144 : ℝ)) 2 (198425645141/200000000000 : ℝ) (496064112853/500000000000 : ℝ) (992128225583/1000000000000 : ℝ) (198425645117/200000000000 : ℝ) (248032056411/250000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33213/262144 : ℝ)) 3 (248032056411/250000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33213/262144 : ℝ)) 4 (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33213/262144 : ℝ)) 5 (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33213/262144 : ℝ)) 6 (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33213/262144 : ℝ)) 7 (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33213/262144 : ℝ))) (176572949143/1000000000000 : ℝ) (3531458983/20000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33213/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176572949143/1000000000000 : ℝ) (3531458983/20000000000 : ℝ) (588286474571/1000000000000 : ℝ) (23531458983/40000000000 : ℝ) (84041168279/200000000000 : ℝ) (105051460351/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33213/262144 : ℝ))) 1 (588286474571/1000000000000 : ℝ) (23531458983/40000000000 : ℝ) (84041168279/200000000000 : ℝ) (105051460351/250000000000 : ℝ) (504246157983/1000000000000 : ℝ) (50424615799/100000000000 : ℝ) (62149192099/125000000000 : ℝ) (621491921/1250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33213/262144 : ℝ))) 2 (504246157983/1000000000000 : ℝ) (50424615799/100000000000 : ℝ) (62149192099/125000000000 : ℝ) (621491921/1250000000 : ℝ) (500719847387/1000000000000 : ℝ) (100143969479/200000000000 : ℝ) (500707430243/1000000000000 : ℝ) (125176857563/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33213/262144 : ℝ))) 3 (500719847387/1000000000000 : ℝ) (100143969479/200000000000 : ℝ) (500707430243/1000000000000 : ℝ) (125176857563/250000000000 : ℝ) (100142727763/200000000000 : ℝ) (62589204853/125000000000 : ℝ) (62589204847/125000000000 : ℝ) (250356819393/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33213/262144 : ℝ))) 4 (100142727763/200000000000 : ℝ) (62589204853/125000000000 : ℝ) (62589204847/125000000000 : ℝ) (250356819393/500000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33213/262144 : ℝ))) 5 (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33213/262144 : ℝ))) 6 (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33213/262144 : ℝ))) 7 (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33213/262144 : ℝ)) hmem 8 (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33213/262144 : ℝ))) hcmem 8 (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33213/262144 : ℝ)) (992128225643/1000000000000 : ℝ) (496064112823/500000000000 : ℝ) (100142727759/200000000000 : ℝ) (100142727761/200000000000 : ℝ) (792759569039/1000000000000 : ℝ) (396379784529/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0432_exp_lower
  have heNumeric : (1027451369267/500000000000 : ℝ)/4 ≤ Real.exp (-10657053495553/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451369267/500000000000 : ℝ)/4 ≤ Real.exp ((8303/65536 : ℝ)-(396379784529/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8303/65536 : ℝ) (33213/262144 : ℝ) (396379784529/500000000000 : ℝ) (1027451369267/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0433; no trusted numerical premise.
theorem cover8_leaf0433_exp_radius : (199604449931824213/200000000000000000 : ℝ) ≤ Real.exp ((-16607/1048576 : ℝ)/8) ∧ Real.exp ((-16607/1048576 : ℝ)/8) ≤ (499011124829560533/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16607/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0433_exp_lower : (460056756480938191/500000000000000000 : ℝ) ≤ Real.exp ((-42628215242739/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628215242739/64000000000000 : ℝ)/8) ≤ (920113512961876383/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628215242739/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0433_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902698061/1000000000000 : ℝ) ≤ 4*Real.exp (33213/262144 : ℝ)*Real.exp (-mu (radius 8 (16607/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902698061/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16607/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0433_exp_radius
  have hrNumeric : (984287087027/1000000000000 : ℝ) ≤ Real.exp (-16607/1048576 : ℝ) ∧ Real.exp (-16607/1048576 : ℝ) ≤ (246071771757/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984287087027/1000000000000 : ℝ) ≤ (radius 8 (16607/131072 : ℝ)) ∧ (radius 8 (16607/131072 : ℝ)) ≤ (246071771757/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16607/131072 : ℝ)) (984287087027/1000000000000 : ℝ) (246071771757/250000000000 : ℝ) (88287782719/500000000000 : ℝ) (35315113089/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16607/131072 : ℝ)) (984287087027/1000000000000 : ℝ) (246071771757/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16607/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984287087027/1000000000000 : ℝ) (246071771757/250000000000 : ℝ) (992143543513/1000000000000 : ℝ) (496071771757/500000000000 : ℝ) (198422487337/200000000000 : ℝ) (992112436687/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16607/131072 : ℝ)) 1 (992143543513/1000000000000 : ℝ) (496071771757/500000000000 : ℝ) (198422487337/200000000000 : ℝ) (992112436687/1000000000000 : ℝ) (992127990099/1000000000000 : ℝ) (992127990101/1000000000000 : ℝ) (992127989977/1000000000000 : ℝ) (992127989979/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16607/131072 : ℝ)) 2 (992127990099/1000000000000 : ℝ) (992127990101/1000000000000 : ℝ) (992127989977/1000000000000 : ℝ) (992127989979/1000000000000 : ℝ) (496063995019/500000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16607/131072 : ℝ)) 3 (496063995019/500000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16607/131072 : ℝ)) 4 (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16607/131072 : ℝ)) 5 (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16607/131072 : ℝ)) 6 (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16607/131072 : ℝ)) 7 (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16607/131072 : ℝ))) (88287782719/500000000000 : ℝ) (35315113089/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16607/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88287782719/500000000000 : ℝ) (35315113089/200000000000 : ℝ) (588287782719/1000000000000 : ℝ) (588287782723/1000000000000 : ℝ) (84041790899/200000000000 : ℝ) (52526119313/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16607/131072 : ℝ))) 1 (588287782719/1000000000000 : ℝ) (588287782723/1000000000000 : ℝ) (84041790899/200000000000 : ℝ) (52526119313/125000000000 : ℝ) (504248368607/1000000000000 : ℝ) (252124184307/500000000000 : ℝ) (497195931317/1000000000000 : ℝ) (19887837253/40000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16607/131072 : ℝ))) 2 (504248368607/1000000000000 : ℝ) (252124184307/500000000000 : ℝ) (497195931317/1000000000000 : ℝ) (19887837253/40000000000 : ℝ) (250361074981/500000000000 : ℝ) (50072214997/100000000000 : ℝ) (250354866761/500000000000 : ℝ) (500709733531/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16607/131072 : ℝ))) 3 (250361074981/500000000000 : ℝ) (50072214997/100000000000 : ℝ) (250354866761/500000000000 : ℝ) (500709733531/1000000000000 : ℝ) (250357970871/500000000000 : ℝ) (500715941751/1000000000000 : ℝ) (500715941703/1000000000000 : ℝ) (500715941713/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16607/131072 : ℝ))) 4 (250357970871/500000000000 : ℝ) (500715941751/1000000000000 : ℝ) (500715941703/1000000000000 : ℝ) (500715941713/1000000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16607/131072 : ℝ))) 5 (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16607/131072 : ℝ))) 6 (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16607/131072 : ℝ))) 7 (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16607/131072 : ℝ)) hmem 8 (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16607/131072 : ℝ))) hcmem 8 (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16607/131072 : ℝ)) (992127990037/1000000000000 : ℝ) (24803199751/25000000000 : ℝ) (250357970861/500000000000 : ℝ) (125178985433/250000000000 : ℝ) (99095425429/125000000000 : ℝ) (792763403451/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0433_exp_lower
  have heNumeric : (2054902698061/1000000000000 : ℝ)/4 ≤ Real.exp (-42628215242739/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902698061/1000000000000 : ℝ)/4 ≤ Real.exp ((33213/262144 : ℝ)-(792763403451/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33213/262144 : ℝ) (16607/131072 : ℝ) (792763403451/1000000000000 : ℝ) (2054902698061/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0434; no trusted numerical premise.
theorem cover8_leaf0434_exp_radius : (998022190172361169/1000000000000000000 : ℝ) ≤ Real.exp ((-33215/2097152 : ℝ)/8) ∧ Real.exp ((-33215/2097152 : ℝ)/8) ≤ (99802219017236117/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33215/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0434_exp_lower : (184022702141341743/200000000000000000 : ℝ) ≤ Real.exp ((-21314108248817/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314108248817/32000000000000 : ℝ)/8) ≤ (230028377676677179/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314108248817/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0434_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902657769/1000000000000 : ℝ) ≤ 4*Real.exp (16607/131072 : ℝ)*Real.exp (-mu (radius 8 (33215/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902657769/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33215/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0434_exp_radius
  have hrNumeric : (984286617683/1000000000000 : ℝ) ≤ Real.exp (-33215/2097152 : ℝ) ∧ Real.exp (-33215/2097152 : ℝ) ≤ (246071654421/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984286617683/1000000000000 : ℝ) ≤ (radius 8 (33215/262144 : ℝ)) ∧ (radius 8 (33215/262144 : ℝ)) ≤ (246071654421/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33215/262144 : ℝ)) (984286617683/1000000000000 : ℝ) (246071654421/250000000000 : ℝ) (176578181687/1000000000000 : ℝ) (88289090847/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33215/262144 : ℝ)) (984286617683/1000000000000 : ℝ) (246071654421/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33215/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984286617683/1000000000000 : ℝ) (246071654421/250000000000 : ℝ) (992143308841/1000000000000 : ℝ) (496071654421/500000000000 : ℝ) (248028050037/250000000000 : ℝ) (992112200149/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33215/262144 : ℝ)) 1 (992143308841/1000000000000 : ℝ) (496071654421/500000000000 : ℝ) (248028050037/250000000000 : ℝ) (992112200149/1000000000000 : ℝ) (496063877247/500000000000 : ℝ) (3875499041/3906250000 : ℝ) (248031938593/250000000000 : ℝ) (496063877187/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33215/262144 : ℝ)) 2 (496063877247/500000000000 : ℝ) (3875499041/3906250000 : ℝ) (248031938593/250000000000 : ℝ) (496063877187/500000000000 : ℝ) (992127754433/1000000000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33215/262144 : ℝ)) 3 (992127754433/1000000000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33215/262144 : ℝ)) 4 (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33215/262144 : ℝ)) 5 (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33215/262144 : ℝ)) 6 (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33215/262144 : ℝ)) 7 (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33215/262144 : ℝ))) (176578181687/1000000000000 : ℝ) (88289090847/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33215/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176578181687/1000000000000 : ℝ) (88289090847/500000000000 : ℝ) (588289090843/1000000000000 : ℝ) (588289090847/1000000000000 : ℝ) (420212067517/1000000000000 : ℝ) (210106033763/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33215/262144 : ℝ))) 1 (588289090843/1000000000000 : ℝ) (588289090847/1000000000000 : ℝ) (420212067517/1000000000000 : ℝ) (210106033763/500000000000 : ℝ) (25212528959/50000000000 : ℝ) (504250579187/1000000000000 : ℝ) (248599162891/500000000000 : ℝ) (49719832579/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33215/262144 : ℝ))) 2 (25212528959/50000000000 : ℝ) (504250579187/1000000000000 : ℝ) (248599162891/500000000000 : ℝ) (49719832579/100000000000 : ℝ) (500724452481/1000000000000 : ℝ) (500724452489/1000000000000 : ℝ) (250356018373/500000000000 : ℝ) (100142407351/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33215/262144 : ℝ))) 3 (500724452481/1000000000000 : ℝ) (500724452489/1000000000000 : ℝ) (250356018373/500000000000 : ℝ) (100142407351/200000000000 : ℝ) (500718244613/1000000000000 : ℝ) (250359122311/500000000000 : ℝ) (20028729783/40000000000 : ℝ) (62589780573/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33215/262144 : ℝ))) 4 (500718244613/1000000000000 : ℝ) (250359122311/500000000000 : ℝ) (20028729783/40000000000 : ℝ) (62589780573/125000000000 : ℝ) (250359122297/500000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33215/262144 : ℝ))) 5 (250359122297/500000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33215/262144 : ℝ))) 6 (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33215/262144 : ℝ))) 7 (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33215/262144 : ℝ)) hmem 8 (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33215/262144 : ℝ))) hcmem 8 (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33215/262144 : ℝ)) (15501996163/15625000000 : ℝ) (198425550887/200000000000 : ℝ) (500718244593/1000000000000 : ℝ) (500718244603/1000000000000 : ℝ) (792767237737/1000000000000 : ℝ) (198191809439/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0434_exp_lower
  have heNumeric : (2054902657769/1000000000000 : ℝ)/4 ≤ Real.exp (-21314108248817/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902657769/1000000000000 : ℝ)/4 ≤ Real.exp ((16607/131072 : ℝ)-(198191809439/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16607/131072 : ℝ) (33215/262144 : ℝ) (198191809439/250000000000 : ℝ) (2054902657769/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0435; no trusted numerical premise.
theorem cover8_leaf0435_exp_radius : (499011065342802409/500000000000000000 : ℝ) ≤ Real.exp ((-519/32768 : ℝ)/8) ∧ Real.exp ((-519/32768 : ℝ)/8) ≤ (998022130685604819/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-519/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0435_exp_lower : (460056754229681009/500000000000000000 : ℝ) ≤ Real.exp ((-42628217748177/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628217748177/64000000000000 : ℝ)/8) ≤ (920113508459362019/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628217748177/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0435_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902617617/1000000000000 : ℝ) ≤ 4*Real.exp (33215/262144 : ℝ)*Real.exp (-mu (radius 8 (519/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902617617/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (519/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0435_exp_radius
  have hrNumeric : (492143074169/500000000000 : ℝ) ≤ Real.exp (-519/32768 : ℝ) ∧ Real.exp (-519/32768 : ℝ) ≤ (984286148339/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492143074169/500000000000 : ℝ) ≤ (radius 8 (519/4096 : ℝ)) ∧ (radius 8 (519/4096 : ℝ)) ≤ (984286148339/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (519/4096 : ℝ)) (492143074169/500000000000 : ℝ) (984286148339/1000000000000 : ℝ) (88290398951/500000000000 : ℝ) (176580797909/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (519/4096 : ℝ)) (492143074169/500000000000 : ℝ) (984286148339/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (519/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492143074169/500000000000 : ℝ) (984286148339/1000000000000 : ℝ) (992143074169/1000000000000 : ℝ) (99214307417/100000000000 : ℝ) (992111963609/1000000000000 : ℝ) (992111963611/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (519/4096 : ℝ)) 1 (992143074169/1000000000000 : ℝ) (99214307417/100000000000 : ℝ) (992111963609/1000000000000 : ℝ) (992111963611/1000000000000 : ℝ) (992127518889/1000000000000 : ℝ) (992127518891/1000000000000 : ℝ) (992127518767/1000000000000 : ℝ) (992127518769/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (519/4096 : ℝ)) 2 (992127518889/1000000000000 : ℝ) (992127518891/1000000000000 : ℝ) (992127518767/1000000000000 : ℝ) (992127518769/1000000000000 : ℝ) (248031879707/250000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (519/4096 : ℝ)) 3 (248031879707/250000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (519/4096 : ℝ)) 4 (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (519/4096 : ℝ)) 5 (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (519/4096 : ℝ)) 6 (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (519/4096 : ℝ)) 7 (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (519/4096 : ℝ))) (88290398951/500000000000 : ℝ) (176580797909/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (519/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88290398951/500000000000 : ℝ) (176580797909/1000000000000 : ℝ) (588290398951/1000000000000 : ℝ) (117658079791/200000000000 : ℝ) (16808607219/40000000000 : ℝ) (105053795121/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (519/4096 : ℝ))) 1 (588290398951/1000000000000 : ℝ) (117658079791/200000000000 : ℝ) (16808607219/40000000000 : ℝ) (105053795121/250000000000 : ℝ) (504252789713/1000000000000 : ℝ) (12606319743/25000000000 : ℝ) (497200720199/1000000000000 : ℝ) (497200720207/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (519/4096 : ℝ))) 2 (504252789713/1000000000000 : ℝ) (12606319743/25000000000 : ℝ) (497200720199/1000000000000 : ℝ) (497200720207/1000000000000 : ℝ) (125181688739/250000000000 : ℝ) (125181688741/250000000000 : ℝ) (250357169963/500000000000 : ℝ) (250357169967/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (519/4096 : ℝ))) 3 (125181688739/250000000000 : ℝ) (125181688741/250000000000 : ℝ) (250357169963/500000000000 : ℝ) (250357169967/500000000000 : ℝ) (500720547441/1000000000000 : ℝ) (500720547449/1000000000000 : ℝ) (250360273701/500000000000 : ℝ) (500720547411/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (519/4096 : ℝ))) 4 (500720547441/1000000000000 : ℝ) (500720547449/1000000000000 : ℝ) (250360273701/500000000000 : ℝ) (500720547411/1000000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (519/4096 : ℝ))) 5 (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (519/4096 : ℝ))) 6 (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (519/4096 : ℝ))) 7 (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (519/4096 : ℝ)) hmem 8 (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (519/4096 : ℝ))) hcmem 8 (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (519/4096 : ℝ)) (992127518827/1000000000000 : ℝ) (99212751883/100000000000 : ℝ) (500720547421/1000000000000 : ℝ) (50072054743/100000000000 : ℝ) (31710842879/40000000000 : ℝ) (792771071993/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0435_exp_lower
  have heNumeric : (2054902617617/1000000000000 : ℝ)/4 ≤ Real.exp (-42628217748177/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902617617/1000000000000 : ℝ)/4 ≤ Real.exp ((33215/262144 : ℝ)-(792771071993/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33215/262144 : ℝ) (519/4096 : ℝ) (792771071993/1000000000000 : ℝ) (2054902617617/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0436; no trusted numerical premise.
theorem cover8_leaf0436_exp_radius : (499011035599426007/500000000000000000 : ℝ) ≤ Real.exp ((-33217/2097152 : ℝ)/8) ∧ Real.exp ((-33217/2097152 : ℝ)/8) ≤ (199604414239770403/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33217/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0436_exp_lower : (920113506221676519/1000000000000000000 : ℝ) ≤ Real.exp ((-666065921771/1000000000000 : ℝ)/8) ∧ Real.exp ((-666065921771/1000000000000 : ℝ)/8) ≤ (23002837655541913/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666065921771/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0436_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902577637/1000000000000 : ℝ) ≤ 4*Real.exp (519/4096 : ℝ)*Real.exp (-mu (radius 8 (33217/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902577637/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33217/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0436_exp_radius
  have hrNumeric : (492142839497/500000000000 : ℝ) ≤ Real.exp (-33217/2097152 : ℝ) ∧ Real.exp (-33217/2097152 : ℝ) ≤ (196857135799/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492142839497/500000000000 : ℝ) ≤ (radius 8 (33217/262144 : ℝ)) ∧ (radius 8 (33217/262144 : ℝ)) ≤ (196857135799/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33217/262144 : ℝ)) (492142839497/500000000000 : ℝ) (196857135799/200000000000 : ℝ) (22072926759/125000000000 : ℝ) (88291707039/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33217/262144 : ℝ)) (492142839497/500000000000 : ℝ) (196857135799/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33217/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492142839497/500000000000 : ℝ) (196857135799/200000000000 : ℝ) (992142839497/1000000000000 : ℝ) (496071419749/500000000000 : ℝ) (31003491471/31250000000 : ℝ) (992111727073/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33217/262144 : ℝ)) 1 (992142839497/1000000000000 : ℝ) (496071419749/500000000000 : ℝ) (31003491471/31250000000 : ℝ) (992111727073/1000000000000 : ℝ) (248031820821/250000000000 : ℝ) (496063641643/500000000000 : ℝ) (496063641581/500000000000 : ℝ) (248031820791/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33217/262144 : ℝ)) 2 (248031820821/250000000000 : ℝ) (496063641643/500000000000 : ℝ) (496063641581/500000000000 : ℝ) (248031820791/250000000000 : ℝ) (992127283223/1000000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33217/262144 : ℝ)) 3 (992127283223/1000000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33217/262144 : ℝ)) 4 (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33217/262144 : ℝ)) 5 (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33217/262144 : ℝ)) 6 (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33217/262144 : ℝ)) 7 (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33217/262144 : ℝ))) (22072926759/125000000000 : ℝ) (88291707039/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33217/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22072926759/125000000000 : ℝ) (88291707039/500000000000 : ℝ) (147072926759/250000000000 : ℝ) (588291707039/1000000000000 : ℝ) (420218293357/1000000000000 : ℝ) (84043658673/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33217/262144 : ℝ))) 1 (147072926759/250000000000 : ℝ) (588291707039/1000000000000 : ℝ) (420218293357/1000000000000 : ℝ) (84043658673/200000000000 : ℝ) (126063750049/250000000000 : ℝ) (252127500101/500000000000 : ℝ) (248601557279/500000000000 : ℝ) (99440622913/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33217/262144 : ℝ))) 2 (126063750049/250000000000 : ℝ) (252127500101/500000000000 : ℝ) (248601557279/500000000000 : ℝ) (99440622913/200000000000 : ℝ) (500729057377/1000000000000 : ℝ) (62591132173/125000000000 : ℝ) (500716643051/1000000000000 : ℝ) (500716643059/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33217/262144 : ℝ))) 3 (500729057377/1000000000000 : ℝ) (62591132173/125000000000 : ℝ) (500716643051/1000000000000 : ℝ) (500716643059/1000000000000 : ℝ) (250361425107/500000000000 : ℝ) (250361425111/500000000000 : ℝ) (20028914007/40000000000 : ℝ) (62590356273/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33217/262144 : ℝ))) 4 (250361425107/500000000000 : ℝ) (250361425111/500000000000 : ℝ) (20028914007/40000000000 : ℝ) (62590356273/125000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33217/262144 : ℝ))) 5 (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33217/262144 : ℝ))) 6 (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33217/262144 : ℝ))) 7 (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33217/262144 : ℝ)) hmem 8 (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33217/262144 : ℝ))) hcmem 8 (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33217/262144 : ℝ)) (496063641611/500000000000 : ℝ) (39685091329/40000000000 : ℝ) (250361425097/500000000000 : ℝ) (500722850203/1000000000000 : ℝ) (792774906129/1000000000000 : ℝ) (396387453073/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0436_exp_lower
  have heNumeric : (2054902577637/1000000000000 : ℝ)/4 ≤ Real.exp (-666065921771/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902577637/1000000000000 : ℝ)/4 ≤ Real.exp ((519/4096 : ℝ)-(396387453073/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (519/4096 : ℝ) (33217/262144 : ℝ) (396387453073/500000000000 : ℝ) (2054902577637/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0437; no trusted numerical premise.
theorem cover8_leaf0437_exp_radius : (199604402342420551/200000000000000000 : ℝ) ≤ Real.exp ((-16609/1048576 : ℝ)/8) ∧ Real.exp ((-16609/1048576 : ℝ)/8) ≤ (249505502928025689/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16609/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0437_exp_lower : (460056751996423559/500000000000000000 : ℝ) ≤ Real.exp ((-42628220233583/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628220233583/64000000000000 : ℝ)/8) ≤ (920113503992847119/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628220233583/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0437_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862817227/125000000000 : ℝ) ≤ 4*Real.exp (33217/262144 : ℝ)*Real.exp (-mu (radius 8 (16609/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256862817227/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16609/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0437_exp_radius
  have hrNumeric : (19685704193/20000000000 : ℝ) ≤ Real.exp (-16609/1048576 : ℝ) ∧ Real.exp (-16609/1048576 : ℝ) ≤ (984285209651/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19685704193/20000000000 : ℝ) ≤ (radius 8 (16609/131072 : ℝ)) ∧ (radius 8 (16609/131072 : ℝ)) ≤ (984285209651/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16609/131072 : ℝ)) (19685704193/20000000000 : ℝ) (984285209651/1000000000000 : ℝ) (176586030201/1000000000000 : ℝ) (176586030207/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16609/131072 : ℝ)) (19685704193/20000000000 : ℝ) (984285209651/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16609/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19685704193/20000000000 : ℝ) (984285209651/1000000000000 : ℝ) (39685704193/40000000000 : ℝ) (496071302413/500000000000 : ℝ) (496055745267/500000000000 : ℝ) (198422298107/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16609/131072 : ℝ)) 1 (39685704193/40000000000 : ℝ) (496071302413/500000000000 : ℝ) (496055745267/500000000000 : ℝ) (198422298107/200000000000 : ℝ) (992127047679/1000000000000 : ℝ) (992127047681/1000000000000 : ℝ) (992127047557/1000000000000 : ℝ) (992127047559/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16609/131072 : ℝ)) 2 (992127047679/1000000000000 : ℝ) (992127047681/1000000000000 : ℝ) (992127047557/1000000000000 : ℝ) (992127047559/1000000000000 : ℝ) (496063523809/500000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16609/131072 : ℝ)) 3 (496063523809/500000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16609/131072 : ℝ)) 4 (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16609/131072 : ℝ)) 5 (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16609/131072 : ℝ)) 6 (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16609/131072 : ℝ)) 7 (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16609/131072 : ℝ))) (176586030201/1000000000000 : ℝ) (176586030207/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16609/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176586030201/1000000000000 : ℝ) (176586030207/1000000000000 : ℝ) (5882930151/10000000000 : ℝ) (9192078361/15625000000 : ℝ) (420221406167/1000000000000 : ℝ) (16808856247/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16609/131072 : ℝ))) 1 (5882930151/10000000000 : ℝ) (9192078361/15625000000 : ℝ) (420221406167/1000000000000 : ℝ) (16808856247/40000000000 : ℝ) (504257210633/1000000000000 : ℝ) (6303215133/12500000000 : ℝ) (248602754431/500000000000 : ℝ) (49720550887/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16609/131072 : ℝ))) 2 (504257210633/1000000000000 : ℝ) (6303215133/12500000000 : ℝ) (248602754431/500000000000 : ℝ) (49720550887/100000000000 : ℝ) (500731359747/1000000000000 : ℝ) (100146271951/200000000000 : ℝ) (250359473063/500000000000 : ℝ) (100143789227/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16609/131072 : ℝ))) 3 (500731359747/1000000000000 : ℝ) (100146271951/200000000000 : ℝ) (250359473063/500000000000 : ℝ) (100143789227/200000000000 : ℝ) (62590644117/125000000000 : ℝ) (100145030589/200000000000 : ℝ) (250362576449/500000000000 : ℝ) (500725152907/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16609/131072 : ℝ))) 4 (62590644117/125000000000 : ℝ) (100145030589/200000000000 : ℝ) (250362576449/500000000000 : ℝ) (500725152907/1000000000000 : ℝ) (500725152917/1000000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16609/131072 : ℝ))) 5 (500725152917/1000000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16609/131072 : ℝ))) 6 (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16609/131072 : ℝ))) 7 (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16609/131072 : ℝ)) hmem 8 (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16609/131072 : ℝ))) hcmem 8 (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16609/131072 : ℝ)) (992127047617/1000000000000 : ℝ) (49606352381/50000000000 : ℝ) (125181288229/250000000000 : ℝ) (250362576463/500000000000 : ℝ) (792778740203/1000000000000 : ℝ) (396389370111/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0437_exp_lower
  have heNumeric : (256862817227/125000000000 : ℝ)/4 ≤ Real.exp (-42628220233583/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862817227/125000000000 : ℝ)/4 ≤ Real.exp ((33217/262144 : ℝ)-(396389370111/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33217/262144 : ℝ) (16609/131072 : ℝ) (396389370111/500000000000 : ℝ) (256862817227/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0438; no trusted numerical premise.
theorem cover8_leaf0438_exp_radius : (499010976112678521/500000000000000000 : ℝ) ≤ Real.exp ((-33219/2097152 : ℝ)/8) ∧ Real.exp ((-33219/2097152 : ℝ)/8) ≤ (998021952225357043/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33219/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0438_exp_lower : (9201135017735639/10000000000000000 : ℝ) ≤ Real.exp ((-4262822146851/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262822146851/6400000000000 : ℝ)/8) ≤ (920113501773563901/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262822146851/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0438_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980499633/200000000000 : ℝ) ≤ 4*Real.exp (16609/131072 : ℝ)*Real.exp (-mu (radius 8 (33219/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980499633/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33219/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0438_exp_radius
  have hrNumeric : (984284740307/1000000000000 : ℝ) ≤ Real.exp (-33219/2097152 : ℝ) ∧ Real.exp (-33219/2097152 : ℝ) ≤ (246071185077/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984284740307/1000000000000 : ℝ) ≤ (radius 8 (33219/262144 : ℝ)) ∧ (radius 8 (33219/262144 : ℝ)) ≤ (246071185077/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33219/262144 : ℝ)) (984284740307/1000000000000 : ℝ) (246071185077/250000000000 : ℝ) (35317729257/200000000000 : ℝ) (176588646291/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33219/262144 : ℝ)) (984284740307/1000000000000 : ℝ) (246071185077/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33219/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984284740307/1000000000000 : ℝ) (246071185077/250000000000 : ℝ) (992142370153/1000000000000 : ℝ) (496071185077/500000000000 : ℝ) (248027813499/250000000000 : ℝ) (496055626999/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33219/262144 : ℝ)) 1 (992142370153/1000000000000 : ℝ) (496071185077/500000000000 : ℝ) (248027813499/250000000000 : ℝ) (496055626999/500000000000 : ℝ) (496063406037/500000000000 : ℝ) (248031703019/250000000000 : ℝ) (62007925747/62500000000 : ℝ) (198425362391/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33219/262144 : ℝ)) 2 (496063406037/500000000000 : ℝ) (248031703019/250000000000 : ℝ) (62007925747/62500000000 : ℝ) (198425362391/200000000000 : ℝ) (992126812013/1000000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33219/262144 : ℝ)) 3 (992126812013/1000000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33219/262144 : ℝ)) 4 (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33219/262144 : ℝ)) 5 (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33219/262144 : ℝ)) 6 (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33219/262144 : ℝ)) 7 (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33219/262144 : ℝ))) (35317729257/200000000000 : ℝ) (176588646291/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33219/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35317729257/200000000000 : ℝ) (176588646291/1000000000000 : ℝ) (294147161571/500000000000 : ℝ) (294147161573/500000000000 : ℝ) (4202245189/10000000000 : ℝ) (105056129727/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33219/262144 : ℝ))) 1 (294147161571/500000000000 : ℝ) (294147161573/500000000000 : ℝ) (4202245189/10000000000 : ℝ) (105056129727/250000000000 : ℝ) (504259421021/1000000000000 : ℝ) (504259421027/1000000000000 : ℝ) (124301975777/250000000000 : ℝ) (124301975779/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33219/262144 : ℝ))) 2 (504259421021/1000000000000 : ℝ) (504259421027/1000000000000 : ℝ) (124301975777/250000000000 : ℝ) (124301975779/250000000000 : ℝ) (31295853879/62500000000 : ℝ) (62591707759/125000000000 : ℝ) (500721249147/1000000000000 : ℝ) (100144249831/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33219/262144 : ℝ))) 3 (31295853879/62500000000 : ℝ) (62591707759/125000000000 : ℝ) (500721249147/1000000000000 : ℝ) (100144249831/200000000000 : ℝ) (100145491121/200000000000 : ℝ) (250363727807/500000000000 : ℝ) (500727455567/1000000000000 : ℝ) (62590931947/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33219/262144 : ℝ))) 4 (100145491121/200000000000 : ℝ) (250363727807/500000000000 : ℝ) (500727455567/1000000000000 : ℝ) (62590931947/125000000000 : ℝ) (250363727793/500000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33219/262144 : ℝ))) 5 (250363727793/500000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33219/262144 : ℝ))) 6 (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33219/262144 : ℝ))) 7 (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33219/262144 : ℝ)) hmem 8 (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33219/262144 : ℝ))) hcmem 8 (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33219/262144 : ℝ)) (248031703003/250000000000 : ℝ) (62007925751/62500000000 : ℝ) (100145491117/200000000000 : ℝ) (100145491119/200000000000 : ℝ) (158556514839/200000000000 : ℝ) (158556514843/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0438_exp_lower
  have heNumeric : (410980499633/200000000000 : ℝ)/4 ≤ Real.exp (-4262822146851/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980499633/200000000000 : ℝ)/4 ≤ Real.exp ((16609/131072 : ℝ)-(158556514843/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16609/131072 : ℝ) (33219/262144 : ℝ) (158556514843/200000000000 : ℝ) (410980499633/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0439; no trusted numerical premise.
theorem cover8_leaf0439_exp_radius : (499010946369307437/500000000000000000 : ℝ) ≤ Real.exp ((-8305/524288 : ℝ)/8) ∧ Real.exp ((-8305/524288 : ℝ)/8) ≤ (7984175141908919/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8305/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0439_exp_lower : (460056749781108333/500000000000000000 : ℝ) ≤ Real.exp ((-42628222699021/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628222699021/64000000000000 : ℝ)/8) ≤ (920113499562216667/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628222699021/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0439_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215701833/31250000000 : ℝ) ≤ 4*Real.exp (33219/262144 : ℝ)*Real.exp (-mu (radius 8 (8305/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (64215701833/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8305/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0439_exp_radius
  have hrNumeric : (984284270963/1000000000000 : ℝ) ≤ Real.exp (-8305/524288 : ℝ) ∧ Real.exp (-8305/524288 : ℝ) ≤ (246071067741/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984284270963/1000000000000 : ℝ) ≤ (radius 8 (8305/65536 : ℝ)) ∧ (radius 8 (8305/65536 : ℝ)) ≤ (246071067741/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8305/65536 : ℝ)) (984284270963/1000000000000 : ℝ) (246071067741/250000000000 : ℝ) (88295631167/500000000000 : ℝ) (176591262341/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8305/65536 : ℝ)) (984284270963/1000000000000 : ℝ) (246071067741/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8305/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984284270963/1000000000000 : ℝ) (246071067741/250000000000 : ℝ) (992142135481/1000000000000 : ℝ) (496071067741/500000000000 : ℝ) (496055508729/500000000000 : ℝ) (49605550873/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8305/65536 : ℝ)) 1 (992142135481/1000000000000 : ℝ) (496071067741/500000000000 : ℝ) (496055508729/500000000000 : ℝ) (49605550873/50000000000 : ℝ) (992126576469/1000000000000 : ℝ) (992126576471/1000000000000 : ℝ) (992126576347/1000000000000 : ℝ) (992126576349/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8305/65536 : ℝ)) 2 (992126576469/1000000000000 : ℝ) (992126576471/1000000000000 : ℝ) (992126576347/1000000000000 : ℝ) (992126576349/1000000000000 : ℝ) (124015822051/125000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8305/65536 : ℝ)) 3 (124015822051/125000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8305/65536 : ℝ)) 4 (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8305/65536 : ℝ)) 5 (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8305/65536 : ℝ)) 6 (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8305/65536 : ℝ)) 7 (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8305/65536 : ℝ))) (88295631167/500000000000 : ℝ) (176591262341/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8305/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88295631167/500000000000 : ℝ) (176591262341/1000000000000 : ℝ) (588295631167/1000000000000 : ℝ) (588295631171/1000000000000 : ℝ) (26264226973/62500000000 : ℝ) (210113815789/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8305/65536 : ℝ))) 1 (588295631167/1000000000000 : ℝ) (588295631171/1000000000000 : ℝ) (26264226973/62500000000 : ℝ) (210113815789/500000000000 : ℝ) (504261631367/1000000000000 : ℝ) (4034093051/8000000000 : ℝ) (99442059461/200000000000 : ℝ) (248605148657/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8305/65536 : ℝ))) 2 (504261631367/1000000000000 : ℝ) (4034093051/8000000000 : ℝ) (99442059461/200000000000 : ℝ) (248605148657/500000000000 : ℝ) (31295997771/62500000000 : ℝ) (100147192869/200000000000 : ℝ) (500723552123/1000000000000 : ℝ) (500723552133/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8305/65536 : ℝ))) 3 (31295997771/62500000000 : ℝ) (100147192869/200000000000 : ℝ) (500723552123/1000000000000 : ℝ) (500723552133/1000000000000 : ℝ) (500729758229/1000000000000 : ℝ) (500729758239/1000000000000 : ℝ) (500729758191/1000000000000 : ℝ) (500729758201/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8305/65536 : ℝ))) 4 (500729758229/1000000000000 : ℝ) (500729758239/1000000000000 : ℝ) (500729758191/1000000000000 : ℝ) (500729758201/1000000000000 : ℝ) (50072975821/100000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8305/65536 : ℝ))) 5 (50072975821/100000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8305/65536 : ℝ))) 6 (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8305/65536 : ℝ))) 7 (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8305/65536 : ℝ)) hmem 8 (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8305/65536 : ℝ))) hcmem 8 (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8305/65536 : ℝ)) (992126576407/1000000000000 : ℝ) (99212657641/100000000000 : ℝ) (500729758209/1000000000000 : ℝ) (25036487911/50000000000 : ℝ) (792786408119/1000000000000 : ℝ) (792786408139/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0439_exp_lower
  have heNumeric : (64215701833/31250000000 : ℝ)/4 ≤ Real.exp (-42628222699021/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215701833/31250000000 : ℝ)/4 ≤ Real.exp ((33219/262144 : ℝ)-(792786408139/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33219/262144 : ℝ) (8305/65536 : ℝ) (792786408139/1000000000000 : ℝ) (64215701833/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0440; no trusted numerical premise.
theorem cover8_leaf0440_exp_radius : (249505458312969063/250000000000000000 : ℝ) ≤ Real.exp ((-33221/2097152 : ℝ)/8) ∧ Real.exp ((-33221/2097152 : ℝ)/8) ≤ (998021833251876253/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33221/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0440_exp_lower : (920113497360875671/1000000000000000000 : ℝ) ≤ Real.exp ((-10657055980991/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657055980991/16000000000000 : ℝ)/8) ≤ (115014187170109459/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657055980991/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0440_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451209663/500000000000 : ℝ) ≤ 4*Real.exp (8305/65536 : ℝ)*Real.exp (-mu (radius 8 (33221/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451209663/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33221/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0440_exp_radius
  have hrNumeric : (49214190081/50000000000 : ℝ) ≤ Real.exp (-33221/2097152 : ℝ) ∧ Real.exp (-33221/2097152 : ℝ) ≤ (984283801621/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49214190081/50000000000 : ℝ) ≤ (radius 8 (33221/262144 : ℝ)) ∧ (radius 8 (33221/262144 : ℝ)) ≤ (984283801621/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33221/262144 : ℝ)) (49214190081/50000000000 : ℝ) (984283801621/1000000000000 : ℝ) (88296939169/500000000000 : ℝ) (22074234793/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33221/262144 : ℝ)) (49214190081/50000000000 : ℝ) (984283801621/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33221/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49214190081/50000000000 : ℝ) (984283801621/1000000000000 : ℝ) (99214190081/100000000000 : ℝ) (992141900811/1000000000000 : ℝ) (992110780921/1000000000000 : ℝ) (496055390461/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33221/262144 : ℝ)) 1 (99214190081/100000000000 : ℝ) (992141900811/1000000000000 : ℝ) (992110780921/1000000000000 : ℝ) (496055390461/500000000000 : ℝ) (198425268173/200000000000 : ℝ) (992126340867/1000000000000 : ℝ) (992126340743/1000000000000 : ℝ) (198425268149/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33221/262144 : ℝ)) 2 (198425268173/200000000000 : ℝ) (992126340867/1000000000000 : ℝ) (992126340743/1000000000000 : ℝ) (198425268149/200000000000 : ℝ) (248031585201/250000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33221/262144 : ℝ)) 3 (248031585201/250000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33221/262144 : ℝ)) 4 (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33221/262144 : ℝ)) 5 (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33221/262144 : ℝ)) 6 (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33221/262144 : ℝ)) 7 (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33221/262144 : ℝ))) (88296939169/500000000000 : ℝ) (22074234793/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33221/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88296939169/500000000000 : ℝ) (22074234793/125000000000 : ℝ) (588296939169/1000000000000 : ℝ) (147074234793/250000000000 : ℝ) (2626442151/6250000000 : ℝ) (420230744169/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33221/262144 : ℝ))) 1 (588296939169/1000000000000 : ℝ) (147074234793/250000000000 : ℝ) (2626442151/6250000000 : ℝ) (420230744169/1000000000000 : ℝ) (3939561263/7812500000 : ℝ) (504263841671/1000000000000 : ℝ) (99442538289/200000000000 : ℝ) (124303172863/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33221/262144 : ℝ))) 2 (3939561263/7812500000 : ℝ) (504263841671/1000000000000 : ℝ) (99442538289/200000000000 : ℝ) (124303172863/250000000000 : ℝ) (250369133277/500000000000 : ℝ) (250369133281/500000000000 : ℝ) (250362927523/500000000000 : ℝ) (250362927527/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33221/262144 : ℝ))) 3 (250369133277/500000000000 : ℝ) (250369133281/500000000000 : ℝ) (250362927523/500000000000 : ℝ) (250362927527/500000000000 : ℝ) (156478769/312500000 : ℝ) (62591507601/125000000000 : ℝ) (500732060761/1000000000000 : ℝ) (50073206077/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33221/262144 : ℝ))) 4 (156478769/312500000 : ℝ) (62591507601/125000000000 : ℝ) (500732060761/1000000000000 : ℝ) (50073206077/100000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33221/262144 : ℝ))) 5 (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33221/262144 : ℝ))) 6 (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33221/262144 : ℝ))) 7 (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33221/262144 : ℝ)) hmem 8 (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33221/262144 : ℝ))) hcmem 8 (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33221/262144 : ℝ)) (992126340803/1000000000000 : ℝ) (496063170403/500000000000 : ℝ) (25036603039/50000000000 : ℝ) (500732060789/1000000000000 : ℝ) (792790241959/1000000000000 : ℝ) (99098780247/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0440_exp_lower
  have heNumeric : (1027451209663/500000000000 : ℝ)/4 ≤ Real.exp (-10657055980991/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451209663/500000000000 : ℝ)/4 ≤ Real.exp ((8305/65536 : ℝ)-(99098780247/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8305/65536 : ℝ) (33221/262144 : ℝ) (99098780247/125000000000 : ℝ) (1027451209663/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0441; no trusted numerical premise.
theorem cover8_leaf0441_exp_radius : (124752721720642647/125000000000000000 : ℝ) ≤ Real.exp ((-16611/1048576 : ℝ)/8) ∧ Real.exp ((-16611/1048576 : ℝ)/8) ≤ (998021773765141177/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16611/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0441_exp_lower : (460056747584080373/500000000000000000 : ℝ) ≤ Real.exp ((-42628225144107/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628225144107/64000000000000 : ℝ)/8) ≤ (920113495168160747/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628225144107/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0441_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902380149/1000000000000 : ℝ) ≤ 4*Real.exp (33221/262144 : ℝ)*Real.exp (-mu (radius 8 (16611/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902380149/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16611/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0441_exp_radius
  have hrNumeric : (984283332277/1000000000000 : ℝ) ≤ Real.exp (-16611/1048576 : ℝ) ∧ Real.exp (-16611/1048576 : ℝ) ≤ (492141666139/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984283332277/1000000000000 : ℝ) ≤ (radius 8 (16611/131072 : ℝ)) ∧ (radius 8 (16611/131072 : ℝ)) ≤ (492141666139/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16611/131072 : ℝ)) (984283332277/1000000000000 : ℝ) (492141666139/500000000000 : ℝ) (176596494301/1000000000000 : ℝ) (44149123577/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16611/131072 : ℝ)) (984283332277/1000000000000 : ℝ) (492141666139/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16611/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984283332277/1000000000000 : ℝ) (492141666139/500000000000 : ℝ) (496070833069/500000000000 : ℝ) (992141666139/1000000000000 : ℝ) (992110544383/1000000000000 : ℝ) (198422108877/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16611/131072 : ℝ)) 1 (496070833069/500000000000 : ℝ) (992141666139/1000000000000 : ℝ) (992110544383/1000000000000 : ℝ) (198422108877/200000000000 : ℝ) (49606305263/50000000000 : ℝ) (496063052631/500000000000 : ℝ) (496063052569/500000000000 : ℝ) (49606305257/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16611/131072 : ℝ)) 2 (49606305263/50000000000 : ℝ) (496063052631/500000000000 : ℝ) (496063052569/500000000000 : ℝ) (49606305257/50000000000 : ℝ) (992126105199/1000000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16611/131072 : ℝ)) 3 (992126105199/1000000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16611/131072 : ℝ)) 4 (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16611/131072 : ℝ)) 5 (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16611/131072 : ℝ)) 6 (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16611/131072 : ℝ)) 7 (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16611/131072 : ℝ))) (176596494301/1000000000000 : ℝ) (44149123577/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16611/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176596494301/1000000000000 : ℝ) (44149123577/250000000000 : ℝ) (11765964943/20000000000 : ℝ) (294149123577/500000000000 : ℝ) (420233856681/1000000000000 : ℝ) (42023385669/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16611/131072 : ℝ))) 1 (11765964943/20000000000 : ℝ) (294149123577/500000000000 : ℝ) (420233856681/1000000000000 : ℝ) (42023385669/100000000000 : ℝ) (100853210383/200000000000 : ℝ) (252133025961/500000000000 : ℝ) (497215085529/1000000000000 : ℝ) (497215085537/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16611/131072 : ℝ))) 2 (100853210383/200000000000 : ℝ) (252133025961/500000000000 : ℝ) (497215085529/1000000000000 : ℝ) (497215085537/1000000000000 : ℝ) (250370284361/500000000000 : ℝ) (50074056873/100000000000 : ℝ) (250364078959/500000000000 : ℝ) (250364078963/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16611/131072 : ℝ))) 3 (250370284361/500000000000 : ℝ) (50074056873/100000000000 : ℝ) (250364078959/500000000000 : ℝ) (250364078963/500000000000 : ℝ) (12518359083/25000000000 : ℝ) (7823974427/15625000000 : ℝ) (500734363281/1000000000000 : ℝ) (50073436329/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16611/131072 : ℝ))) 4 (12518359083/25000000000 : ℝ) (7823974427/15625000000 : ℝ) (500734363281/1000000000000 : ℝ) (50073436329/100000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16611/131072 : ℝ))) 5 (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16611/131072 : ℝ))) 6 (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16611/131072 : ℝ))) 7 (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16611/131072 : ℝ)) hmem 8 (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16611/131072 : ℝ))) hcmem 8 (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16611/131072 : ℝ)) (496063052599/500000000000 : ℝ) (992126105201/1000000000000 : ℝ) (5007343633/10000000000 : ℝ) (500734363309/1000000000000 : ℝ) (792794075721/1000000000000 : ℝ) (396397037869/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0441_exp_lower
  have heNumeric : (2054902380149/1000000000000 : ℝ)/4 ≤ Real.exp (-42628225144107/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902380149/1000000000000 : ℝ)/4 ≤ Real.exp ((33221/262144 : ℝ)-(396397037869/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33221/262144 : ℝ) (16611/131072 : ℝ) (396397037869/500000000000 : ℝ) (2054902380149/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0442; no trusted numerical premise.
theorem cover8_leaf0442_exp_radius : (199604342855681929/200000000000000000 : ℝ) ≤ Real.exp ((-33223/2097152 : ℝ)/8) ∧ Real.exp ((-33223/2097152 : ℝ)/8) ≤ (499010857139204823/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33223/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0442_exp_lower : (92011349298407189/100000000000000000 : ℝ) ≤ Real.exp ((-852564527189/1280000000000 : ℝ)/8) ∧ Real.exp ((-852564527189/1280000000000 : ℝ)/8) ≤ (920113492984071891/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-852564527189/1280000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0442_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902341127/1000000000000 : ℝ) ≤ 4*Real.exp (16611/131072 : ℝ)*Real.exp (-mu (radius 8 (33223/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902341127/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33223/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0442_exp_radius
  have hrNumeric : (492141431467/500000000000 : ℝ) ≤ Real.exp (-33223/2097152 : ℝ) ∧ Real.exp (-33223/2097152 : ℝ) ≤ (196856572587/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492141431467/500000000000 : ℝ) ≤ (radius 8 (33223/262144 : ℝ)) ∧ (radius 8 (33223/262144 : ℝ)) ≤ (196856572587/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33223/262144 : ℝ)) (492141431467/500000000000 : ℝ) (196856572587/200000000000 : ℝ) (7063964409/40000000000 : ℝ) (22074888779/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33223/262144 : ℝ)) (492141431467/500000000000 : ℝ) (196856572587/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33223/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492141431467/500000000000 : ℝ) (196856572587/200000000000 : ℝ) (992141431467/1000000000000 : ℝ) (248035357867/250000000000 : ℝ) (198422061569/200000000000 : ℝ) (992110307847/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33223/262144 : ℝ)) 1 (992141431467/1000000000000 : ℝ) (248035357867/250000000000 : ℝ) (198422061569/200000000000 : ℝ) (992110307847/1000000000000 : ℝ) (124015733707/125000000000 : ℝ) (496062934829/500000000000 : ℝ) (992125869533/1000000000000 : ℝ) (31003933423/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33223/262144 : ℝ)) 2 (124015733707/125000000000 : ℝ) (496062934829/500000000000 : ℝ) (992125869533/1000000000000 : ℝ) (31003933423/31250000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33223/262144 : ℝ)) 3 (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33223/262144 : ℝ)) 4 (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33223/262144 : ℝ)) 5 (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33223/262144 : ℝ)) 6 (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33223/262144 : ℝ)) 7 (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33223/262144 : ℝ))) (7063964409/40000000000 : ℝ) (22074888779/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33223/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7063964409/40000000000 : ℝ) (22074888779/125000000000 : ℝ) (73537444389/125000000000 : ℝ) (147074888779/250000000000 : ℝ) (420236969131/1000000000000 : ℝ) (420236969141/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33223/262144 : ℝ))) 1 (73537444389/125000000000 : ℝ) (147074888779/250000000000 : ℝ) (420236969131/1000000000000 : ℝ) (420236969141/1000000000000 : ℝ) (504268262121/1000000000000 : ℝ) (504268262129/1000000000000 : ℝ) (497217479561/1000000000000 : ℝ) (497217479569/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33223/262144 : ℝ))) 2 (504268262121/1000000000000 : ℝ) (504268262129/1000000000000 : ℝ) (497217479561/1000000000000 : ℝ) (497217479569/1000000000000 : ℝ) (500742870841/1000000000000 : ℝ) (500742870849/1000000000000 : ℝ) (500730460741/1000000000000 : ℝ) (2002921843/4000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33223/262144 : ℝ))) 3 (500742870841/1000000000000 : ℝ) (500742870849/1000000000000 : ℝ) (500730460741/1000000000000 : ℝ) (2002921843/4000000000 : ℝ) (500736665791/1000000000000 : ℝ) (2503683329/5000000000 : ℝ) (62592083219/125000000000 : ℝ) (250368332881/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33223/262144 : ℝ))) 4 (500736665791/1000000000000 : ℝ) (2503683329/5000000000 : ℝ) (62592083219/125000000000 : ℝ) (250368332881/500000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33223/262144 : ℝ))) 5 (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33223/262144 : ℝ))) 6 (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33223/262144 : ℝ))) 7 (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33223/262144 : ℝ)) hmem 8 (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33223/262144 : ℝ))) hcmem 8 (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33223/262144 : ℝ)) (496062934797/500000000000 : ℝ) (992125869597/1000000000000 : ℝ) (500736665771/1000000000000 : ℝ) (500736665781/1000000000000 : ℝ) (396398954703/500000000000 : ℝ) (31711916377/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0442_exp_lower
  have heNumeric : (2054902341127/1000000000000 : ℝ)/4 ≤ Real.exp (-852564527189/1280000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902341127/1000000000000 : ℝ)/4 ≤ Real.exp ((16611/131072 : ℝ)-(31711916377/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16611/131072 : ℝ) (33223/262144 : ℝ) (31711916377/40000000000 : ℝ) (2054902341127/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0443; no trusted numerical premise.
theorem cover8_leaf0443_exp_radius : (49901082739584083/50000000000000000 : ℝ) ≤ Real.exp ((-4153/262144 : ℝ)/8) ∧ Real.exp ((-4153/262144 : ℝ)/8) ≤ (998021654791681661/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4153/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0443_exp_lower : (460056745404994637/500000000000000000 : ℝ) ≤ Real.exp ((-1705129102769/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705129102769/2560000000000 : ℝ)/8) ≤ (36804539632399571/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705129102769/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0443_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725575571/250000000000 : ℝ) ≤ 4*Real.exp (33223/262144 : ℝ)*Real.exp (-mu (radius 8 (4153/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513725575571/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4153/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0443_exp_radius
  have hrNumeric : (123035299199/125000000000 : ℝ) ≤ Real.exp (-4153/262144 : ℝ) ∧ Real.exp (-4153/262144 : ℝ) ≤ (984282393593/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123035299199/125000000000 : ℝ) ≤ (radius 8 (4153/32768 : ℝ)) ∧ (radius 8 (4153/32768 : ℝ)) ≤ (984282393593/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4153/32768 : ℝ)) (123035299199/125000000000 : ℝ) (984282393593/1000000000000 : ℝ) (176601726103/1000000000000 : ℝ) (17660172611/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4153/32768 : ℝ)) (123035299199/125000000000 : ℝ) (984282393593/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4153/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123035299199/125000000000 : ℝ) (984282393593/1000000000000 : ℝ) (248035299199/250000000000 : ℝ) (992141196797/1000000000000 : ℝ) (248027517827/250000000000 : ℝ) (99211007131/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4153/32768 : ℝ)) 1 (248035299199/250000000000 : ℝ) (992141196797/1000000000000 : ℝ) (248027517827/250000000000 : ℝ) (99211007131/100000000000 : ℝ) (248031408513/250000000000 : ℝ) (496062817027/500000000000 : ℝ) (992125633929/1000000000000 : ℝ) (248031408483/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4153/32768 : ℝ)) 2 (248031408513/250000000000 : ℝ) (496062817027/500000000000 : ℝ) (992125633929/1000000000000 : ℝ) (248031408483/250000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4153/32768 : ℝ)) 3 (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4153/32768 : ℝ)) 4 (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4153/32768 : ℝ)) 5 (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4153/32768 : ℝ)) 6 (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4153/32768 : ℝ)) 7 (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4153/32768 : ℝ))) (176601726103/1000000000000 : ℝ) (17660172611/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4153/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176601726103/1000000000000 : ℝ) (17660172611/100000000000 : ℝ) (588300863051/1000000000000 : ℝ) (117660172611/200000000000 : ℝ) (13132502547/31250000000 : ℝ) (420240081513/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4153/32768 : ℝ))) 1 (588300863051/1000000000000 : ℝ) (117660172611/200000000000 : ℝ) (13132502547/31250000000 : ℝ) (420240081513/1000000000000 : ℝ) (504270472277/1000000000000 : ℝ) (126067618071/250000000000 : ℝ) (248609936767/500000000000 : ℝ) (248609936771/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4153/32768 : ℝ))) 2 (504270472277/1000000000000 : ℝ) (126067618071/250000000000 : ℝ) (248609936767/500000000000 : ℝ) (248609936771/500000000000 : ℝ) (100149034581/200000000000 : ℝ) (500745172913/1000000000000 : ℝ) (50073276351/100000000000 : ℝ) (250366381759/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4153/32768 : ℝ))) 3 (100149034581/200000000000 : ℝ) (500745172913/1000000000000 : ℝ) (50073276351/100000000000 : ℝ) (250366381759/500000000000 : ℝ) (500738968207/1000000000000 : ℝ) (62592371027/125000000000 : ℝ) (500738968169/1000000000000 : ℝ) (250369484089/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4153/32768 : ℝ))) 4 (500738968207/1000000000000 : ℝ) (62592371027/125000000000 : ℝ) (500738968169/1000000000000 : ℝ) (250369484089/500000000000 : ℝ) (125184742047/250000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4153/32768 : ℝ))) 5 (125184742047/250000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4153/32768 : ℝ))) 6 (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4153/32768 : ℝ))) 7 (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4153/32768 : ℝ)) hmem 8 (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4153/32768 : ℝ))) hcmem 8 (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4153/32768 : ℝ)) (99212563399/100000000000 : ℝ) (992125633993/1000000000000 : ℝ) (500738968187/1000000000000 : ℝ) (500738968197/1000000000000 : ℝ) (396400871503/500000000000 : ℝ) (31712069721/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0443_exp_lower
  have heNumeric : (513725575571/250000000000 : ℝ)/4 ≤ Real.exp (-1705129102769/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725575571/250000000000 : ℝ)/4 ≤ Real.exp ((33223/262144 : ℝ)-(31712069721/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33223/262144 : ℝ) (4153/32768 : ℝ) (31712069721/40000000000 : ℝ) (513725575571/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0444; no trusted numerical premise.
theorem cover8_leaf0444_exp_radius : (998021595304957221/1000000000000000000 : ℝ) ≤ Real.exp ((-33225/2097152 : ℝ)/8) ∧ Real.exp ((-33225/2097152 : ℝ)/8) ≤ (499010797652478611/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33225/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0444_exp_lower : (460056744322266363/500000000000000000 : ℝ) ≤ Real.exp ((-213141143871/320000000000 : ℝ)/8) ∧ Real.exp ((-213141143871/320000000000 : ℝ)/8) ≤ (920113488644532727/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-213141143871/320000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0444_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980452719/200000000000 : ℝ) ≤ 4*Real.exp (4153/32768 : ℝ)*Real.exp (-mu (radius 8 (33225/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980452719/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33225/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0444_exp_radius
  have hrNumeric : (3937127697/4000000000 : ℝ) ≤ Real.exp (-33225/2097152 : ℝ) ∧ Real.exp (-33225/2097152 : ℝ) ≤ (984281924251/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (3937127697/4000000000 : ℝ) ≤ (radius 8 (33225/262144 : ℝ)) ∧ (radius 8 (33225/262144 : ℝ)) ≤ (984281924251/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33225/262144 : ℝ)) (3937127697/4000000000 : ℝ) (984281924251/1000000000000 : ℝ) (176604341941/1000000000000 : ℝ) (44151085487/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33225/262144 : ℝ)) (3937127697/4000000000 : ℝ) (984281924251/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33225/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (3937127697/4000000000 : ℝ) (984281924251/1000000000000 : ℝ) (7937127697/8000000000 : ℝ) (496070481063/500000000000 : ℝ) (992109834771/1000000000000 : ℝ) (248027458693/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33225/262144 : ℝ)) 1 (7937127697/8000000000 : ℝ) (496070481063/500000000000 : ℝ) (992109834771/1000000000000 : ℝ) (248027458693/250000000000 : ℝ) (62007837403/62500000000 : ℝ) (992125398449/1000000000000 : ℝ) (39685015933/40000000000 : ℝ) (992125398327/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33225/262144 : ℝ)) 2 (62007837403/62500000000 : ℝ) (992125398449/1000000000000 : ℝ) (39685015933/40000000000 : ℝ) (992125398327/1000000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33225/262144 : ℝ)) 3 (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33225/262144 : ℝ)) 4 (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33225/262144 : ℝ)) 5 (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33225/262144 : ℝ)) 6 (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33225/262144 : ℝ)) 7 (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33225/262144 : ℝ))) (176604341941/1000000000000 : ℝ) (44151085487/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33225/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176604341941/1000000000000 : ℝ) (44151085487/250000000000 : ℝ) (58830217097/100000000000 : ℝ) (294151085487/500000000000 : ℝ) (210121596903/500000000000 : ℝ) (52530399227/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33225/262144 : ℝ))) 1 (58830217097/100000000000 : ℝ) (294151085487/500000000000 : ℝ) (210121596903/500000000000 : ℝ) (52530399227/125000000000 : ℝ) (126068170597/250000000000 : ℝ) (100854536479/200000000000 : ℝ) (497222267453/1000000000000 : ℝ) (497222267461/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33225/262144 : ℝ))) 2 (126068170597/250000000000 : ℝ) (100854536479/200000000000 : ℝ) (497222267453/1000000000000 : ℝ) (497222267461/1000000000000 : ℝ) (12518686873/25000000000 : ℝ) (31296717183/62500000000 : ℝ) (500735066229/1000000000000 : ℝ) (500735066237/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33225/262144 : ℝ))) 3 (12518686873/25000000000 : ℝ) (31296717183/62500000000 : ℝ) (500735066229/1000000000000 : ℝ) (500735066237/1000000000000 : ℝ) (250370635287/500000000000 : ℝ) (500741270583/1000000000000 : ℝ) (62592658817/125000000000 : ℝ) (100148254109/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33225/262144 : ℝ))) 4 (250370635287/500000000000 : ℝ) (500741270583/1000000000000 : ℝ) (62592658817/125000000000 : ℝ) (100148254109/200000000000 : ℝ) (100148254111/200000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33225/262144 : ℝ))) 5 (100148254111/200000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33225/262144 : ℝ))) 6 (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33225/262144 : ℝ))) 7 (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33225/262144 : ℝ)) hmem 8 (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33225/262144 : ℝ))) hcmem 8 (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33225/262144 : ℝ)) (496062699193/500000000000 : ℝ) (248031349597/250000000000 : ℝ) (250370635277/500000000000 : ℝ) (125185317641/250000000000 : ℝ) (792805576531/1000000000000 : ℝ) (15856111531/20000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0444_exp_lower
  have heNumeric : (410980452719/200000000000 : ℝ)/4 ≤ Real.exp (-213141143871/320000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980452719/200000000000 : ℝ)/4 ≤ Real.exp ((4153/32768 : ℝ)-(15856111531/20000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4153/32768 : ℝ) (33225/262144 : ℝ) (15856111531/20000000000 : ℝ) (410980452719/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0445; no trusted numerical premise.
theorem cover8_leaf0445_exp_radius : (124752691977279541/125000000000000000 : ℝ) ≤ Real.exp ((-16613/1048576 : ℝ)/8) ∧ Real.exp ((-16613/1048576 : ℝ)/8) ≤ (998021535818236329/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16613/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0445_exp_lower : (460056743243908631/500000000000000000 : ℝ) ≤ Real.exp ((-42628229974311/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628229974311/64000000000000 : ℝ)/8) ≤ (920113486487817263/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628229974311/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0445_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451112531/500000000000 : ℝ) ≤ 4*Real.exp (33225/262144 : ℝ)*Real.exp (-mu (radius 8 (16613/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451112531/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16613/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0445_exp_radius
  have hrNumeric : (246070363727/250000000000 : ℝ) ≤ Real.exp (-16613/1048576 : ℝ) ∧ Real.exp (-16613/1048576 : ℝ) ≤ (984281454909/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246070363727/250000000000 : ℝ) ≤ (radius 8 (16613/131072 : ℝ)) ∧ (radius 8 (16613/131072 : ℝ)) ≤ (984281454909/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16613/131072 : ℝ)) (246070363727/250000000000 : ℝ) (984281454909/1000000000000 : ℝ) (8830347887/50000000000 : ℝ) (88303478873/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16613/131072 : ℝ)) (246070363727/250000000000 : ℝ) (984281454909/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16613/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246070363727/250000000000 : ℝ) (984281454909/1000000000000 : ℝ) (496070363727/500000000000 : ℝ) (198428145491/200000000000 : ℝ) (992109598233/1000000000000 : ℝ) (198421919647/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16613/131072 : ℝ)) 1 (496070363727/500000000000 : ℝ) (198428145491/200000000000 : ℝ) (992109598233/1000000000000 : ℝ) (198421919647/200000000000 : ℝ) (992125162843/1000000000000 : ℝ) (198425032569/200000000000 : ℝ) (992125162721/1000000000000 : ℝ) (992125162723/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16613/131072 : ℝ)) 2 (992125162843/1000000000000 : ℝ) (198425032569/200000000000 : ℝ) (992125162721/1000000000000 : ℝ) (992125162723/1000000000000 : ℝ) (496062581391/500000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16613/131072 : ℝ)) 3 (496062581391/500000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16613/131072 : ℝ)) 4 (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16613/131072 : ℝ)) 5 (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16613/131072 : ℝ)) 6 (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16613/131072 : ℝ)) 7 (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16613/131072 : ℝ))) (8830347887/50000000000 : ℝ) (88303478873/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16613/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (8830347887/50000000000 : ℝ) (88303478873/500000000000 : ℝ) (58830347887/100000000000 : ℝ) (588303478873/1000000000000 : ℝ) (420246306039/1000000000000 : ℝ) (420246306047/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16613/131072 : ℝ))) 1 (58830347887/100000000000 : ℝ) (588303478873/1000000000000 : ℝ) (420246306039/1000000000000 : ℝ) (420246306047/1000000000000 : ℝ) (252137446227/500000000000 : ℝ) (25213744623/50000000000 : ℝ) (12430616533/25000000000 : ℝ) (497224661327/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16613/131072 : ℝ))) 2 (252137446227/500000000000 : ℝ) (25213744623/50000000000 : ℝ) (12430616533/25000000000 : ℝ) (497224661327/1000000000000 : ℝ) (500749776887/1000000000000 : ℝ) (250374888447/500000000000 : ℝ) (500737368899/1000000000000 : ℝ) (500737368907/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16613/131072 : ℝ))) 3 (500749776887/1000000000000 : ℝ) (250374888447/500000000000 : ℝ) (500737368899/1000000000000 : ℝ) (500737368907/1000000000000 : ℝ) (500743572893/1000000000000 : ℝ) (500743572901/1000000000000 : ℝ) (250371786427/500000000000 : ℝ) (500743572863/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16613/131072 : ℝ))) 4 (500743572893/1000000000000 : ℝ) (500743572901/1000000000000 : ℝ) (250371786427/500000000000 : ℝ) (500743572863/1000000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16613/131072 : ℝ))) 5 (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16613/131072 : ℝ))) 6 (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16613/131072 : ℝ))) 7 (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16613/131072 : ℝ)) hmem 8 (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16613/131072 : ℝ))) hcmem 8 (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16613/131072 : ℝ)) (992125162781/1000000000000 : ℝ) (31003911337/31250000000 : ℝ) (500743572873/1000000000000 : ℝ) (250371786441/500000000000 : ℝ) (792809409981/1000000000000 : ℝ) (792809409999/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0445_exp_lower
  have heNumeric : (1027451112531/500000000000 : ℝ)/4 ≤ Real.exp (-42628229974311/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451112531/500000000000 : ℝ)/4 ≤ Real.exp ((33225/262144 : ℝ)-(792809409999/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33225/262144 : ℝ) (16613/131072 : ℝ) (792809409999/1000000000000 : ℝ) (1027451112531/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0446; no trusted numerical premise.
theorem cover8_leaf0446_exp_radius : (49901073816575949/50000000000000000 : ℝ) ≤ Real.exp ((-33227/2097152 : ℝ)/8) ∧ Real.exp ((-33227/2097152 : ℝ)/8) ≤ (998021476331518981/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33227/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0446_exp_lower : (920113484340072909/1000000000000000000 : ℝ) ≤ Real.exp ((-4262823116943/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262823116943/6400000000000 : ℝ)/8) ≤ (92011348434007291/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262823116943/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0446_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902186689/1000000000000 : ℝ) ≤ 4*Real.exp (16613/131072 : ℝ)*Real.exp (-mu (radius 8 (33227/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902186689/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33227/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0446_exp_radius
  have hrNumeric : (492140492783/500000000000 : ℝ) ≤ Real.exp (-33227/2097152 : ℝ) ∧ Real.exp (-33227/2097152 : ℝ) ≤ (984280985567/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492140492783/500000000000 : ℝ) ≤ (radius 8 (33227/262144 : ℝ)) ∧ (radius 8 (33227/262144 : ℝ)) ≤ (984280985567/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33227/262144 : ℝ)) (492140492783/500000000000 : ℝ) (984280985567/1000000000000 : ℝ) (88304786749/500000000000 : ℝ) (1379762293/7812500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33227/262144 : ℝ)) (492140492783/500000000000 : ℝ) (984280985567/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33227/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492140492783/500000000000 : ℝ) (984280985567/1000000000000 : ℝ) (992140492783/1000000000000 : ℝ) (62008780799/62500000000 : ℝ) (31003417553/31250000000 : ℝ) (496054680849/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33227/262144 : ℝ)) 1 (992140492783/1000000000000 : ℝ) (62008780799/62500000000 : ℝ) (31003417553/31250000000 : ℝ) (496054680849/500000000000 : ℝ) (992124927239/1000000000000 : ℝ) (992124927241/1000000000000 : ℝ) (992124927117/1000000000000 : ℝ) (992124927119/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33227/262144 : ℝ)) 2 (992124927239/1000000000000 : ℝ) (992124927241/1000000000000 : ℝ) (992124927117/1000000000000 : ℝ) (992124927119/1000000000000 : ℝ) (496062463589/500000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33227/262144 : ℝ)) 3 (496062463589/500000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33227/262144 : ℝ)) 4 (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33227/262144 : ℝ)) 5 (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33227/262144 : ℝ)) 6 (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33227/262144 : ℝ)) 7 (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33227/262144 : ℝ))) (88304786749/500000000000 : ℝ) (1379762293/7812500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33227/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88304786749/500000000000 : ℝ) (1379762293/7812500000 : ℝ) (588304786749/1000000000000 : ℝ) (9192262293/15625000000 : ℝ) (2101247091/5000000000 : ℝ) (13132794319/31250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33227/262144 : ℝ))) 1 (588304786749/1000000000000 : ℝ) (9192262293/15625000000 : ℝ) (2101247091/5000000000 : ℝ) (13132794319/31250000000 : ℝ) (252138551237/500000000000 : ℝ) (6303463781/12500000000 : ℝ) (124306763783/250000000000 : ℝ) (497227055139/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33227/262144 : ℝ))) 2 (252138551237/500000000000 : ℝ) (6303463781/12500000000 : ℝ) (124306763783/250000000000 : ℝ) (497227055139/1000000000000 : ℝ) (500752078803/1000000000000 : ℝ) (50075207881/100000000000 : ℝ) (500739671519/1000000000000 : ℝ) (500739671527/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33227/262144 : ℝ))) 3 (500752078803/1000000000000 : ℝ) (50075207881/100000000000 : ℝ) (500739671519/1000000000000 : ℝ) (500739671527/1000000000000 : ℝ) (500745875161/1000000000000 : ℝ) (500745875169/1000000000000 : ℝ) (250372937561/500000000000 : ℝ) (500745875131/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33227/262144 : ℝ))) 4 (500745875161/1000000000000 : ℝ) (500745875169/1000000000000 : ℝ) (250372937561/500000000000 : ℝ) (500745875131/1000000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33227/262144 : ℝ))) 5 (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33227/262144 : ℝ))) 6 (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33227/262144 : ℝ))) 7 (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33227/262144 : ℝ)) hmem 8 (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33227/262144 : ℝ))) hcmem 8 (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33227/262144 : ℝ)) (992124927177/1000000000000 : ℝ) (49606246359/50000000000 : ℝ) (500745875141/1000000000000 : ℝ) (10014917503/20000000000 : ℝ) (792813243353/1000000000000 : ℝ) (79281324337/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0446_exp_lower
  have heNumeric : (2054902186689/1000000000000 : ℝ)/4 ≤ Real.exp (-4262823116943/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902186689/1000000000000 : ℝ)/4 ≤ Real.exp ((16613/131072 : ℝ)-(79281324337/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16613/131072 : ℝ) (33227/262144 : ℝ) (79281324337/100000000000 : ℝ) (2054902186689/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0447; no trusted numerical premise.
theorem cover8_leaf0447_exp_radius : (499010708422402589/500000000000000000 : ℝ) ≤ Real.exp ((-8307/524288 : ℝ)/8) ∧ Real.exp ((-8307/524288 : ℝ)/8) ≤ (998021416844805179/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8307/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0447_exp_lower : (920113482200839611/1000000000000000000 : ℝ) ≤ Real.exp ((-42628232359813/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628232359813/64000000000000 : ℝ)/8) ≤ (230028370550209903/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628232359813/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0447_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902148469/1000000000000 : ℝ) ≤ 4*Real.exp (33227/262144 : ℝ)*Real.exp (-mu (radius 8 (8307/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902148469/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8307/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0447_exp_radius
  have hrNumeric : (7689691533/7812500000 : ℝ) ≤ Real.exp (-8307/524288 : ℝ) ∧ Real.exp (-8307/524288 : ℝ) ≤ (39371220649/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7689691533/7812500000 : ℝ) ≤ (radius 8 (8307/65536 : ℝ)) ∧ (radius 8 (8307/65536 : ℝ)) ≤ (39371220649/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8307/65536 : ℝ)) (7689691533/7812500000 : ℝ) (39371220649/40000000000 : ℝ) (5519130913/31250000000 : ℝ) (176612189223/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8307/65536 : ℝ)) (7689691533/7812500000 : ℝ) (39371220649/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8307/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7689691533/7812500000 : ℝ) (39371220649/40000000000 : ℝ) (15502191533/15625000000 : ℝ) (992140258113/1000000000000 : ℝ) (992109125159/1000000000000 : ℝ) (24802728129/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8307/65536 : ℝ)) 1 (15502191533/15625000000 : ℝ) (992140258113/1000000000000 : ℝ) (992109125159/1000000000000 : ℝ) (24802728129/25000000000 : ℝ) (198424938327/200000000000 : ℝ) (992124691637/1000000000000 : ℝ) (992124691513/1000000000000 : ℝ) (198424938303/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8307/65536 : ℝ)) 2 (198424938327/200000000000 : ℝ) (992124691637/1000000000000 : ℝ) (992124691513/1000000000000 : ℝ) (198424938303/200000000000 : ℝ) (496062345787/500000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8307/65536 : ℝ)) 3 (496062345787/500000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8307/65536 : ℝ)) 4 (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8307/65536 : ℝ)) 5 (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8307/65536 : ℝ)) 6 (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8307/65536 : ℝ)) 7 (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8307/65536 : ℝ))) (5519130913/31250000000 : ℝ) (176612189223/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8307/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (5519130913/31250000000 : ℝ) (176612189223/1000000000000 : ℝ) (36769130913/62500000000 : ℝ) (147076523653/250000000000 : ℝ) (420252530291/1000000000000 : ℝ) (4202525303/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8307/65536 : ℝ))) 1 (36769130913/62500000000 : ℝ) (147076523653/250000000000 : ℝ) (420252530291/1000000000000 : ℝ) (4202525303/10000000000 : ℝ) (504279312449/1000000000000 : ℝ) (63034914057/125000000000 : ℝ) (497229448891/1000000000000 : ℝ) (497229448899/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8307/65536 : ℝ))) 2 (504279312449/1000000000000 : ℝ) (63034914057/125000000000 : ℝ) (497229448891/1000000000000 : ℝ) (497229448899/1000000000000 : ℝ) (50075438067/100000000000 : ℝ) (250377190339/500000000000 : ℝ) (50074197409/100000000000 : ℝ) (500741974099/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8307/65536 : ℝ))) 3 (50075438067/100000000000 : ℝ) (250377190339/500000000000 : ℝ) (50074197409/100000000000 : ℝ) (500741974099/1000000000000 : ℝ) (25037408869/50000000000 : ℝ) (500748177389/1000000000000 : ℝ) (500748177341/1000000000000 : ℝ) (500748177351/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8307/65536 : ℝ))) 4 (25037408869/50000000000 : ℝ) (500748177389/1000000000000 : ℝ) (500748177341/1000000000000 : ℝ) (500748177351/1000000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8307/65536 : ℝ))) 5 (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8307/65536 : ℝ))) 6 (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8307/65536 : ℝ))) 7 (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8307/65536 : ℝ)) hmem 8 (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8307/65536 : ℝ))) hcmem 8 (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8307/65536 : ℝ)) (992124691573/1000000000000 : ℝ) (124015586447/125000000000 : ℝ) (6259352217/12500000000 : ℝ) (50074817737/100000000000 : ℝ) (99102134581/125000000000 : ℝ) (792817076667/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0447_exp_lower
  have heNumeric : (2054902148469/1000000000000 : ℝ)/4 ≤ Real.exp (-42628232359813/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902148469/1000000000000 : ℝ)/4 ≤ Real.exp ((33227/262144 : ℝ)-(792817076667/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33227/262144 : ℝ) (8307/65536 : ℝ) (792817076667/1000000000000 : ℝ) (2054902148469/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0448; no trusted numerical premise.
theorem cover8_leaf0448_exp_radius : (499010678679047461/500000000000000000 : ℝ) ≤ Real.exp ((-33229/2097152 : ℝ)/8) ∧ Real.exp ((-33229/2097152 : ℝ)/8) ≤ (998021357358094923/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33229/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0448_exp_lower : (920113480071727567/1000000000000000000 : ℝ) ≤ Real.exp ((-10657058386141/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657058386141/16000000000000 : ℝ)/8) ≤ (57507092504482973/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657058386141/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0448_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902110429/1000000000000 : ℝ) ≤ 4*Real.exp (8307/65536 : ℝ)*Real.exp (-mu (radius 8 (33229/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902110429/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33229/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0448_exp_radius
  have hrNumeric : (984280046883/1000000000000 : ℝ) ≤ Real.exp (-33229/2097152 : ℝ) ∧ Real.exp (-33229/2097152 : ℝ) ≤ (246070011721/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984280046883/1000000000000 : ℝ) ≤ (radius 8 (33229/262144 : ℝ)) ∧ (radius 8 (33229/262144 : ℝ)) ≤ (246070011721/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33229/262144 : ℝ)) (984280046883/1000000000000 : ℝ) (246070011721/250000000000 : ℝ) (176614804889/1000000000000 : ℝ) (35322960979/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33229/262144 : ℝ)) (984280046883/1000000000000 : ℝ) (246070011721/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33229/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984280046883/1000000000000 : ℝ) (246070011721/250000000000 : ℝ) (992140023441/1000000000000 : ℝ) (496070011721/500000000000 : ℝ) (496054444311/500000000000 : ℝ) (992108888623/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33229/262144 : ℝ)) 1 (992140023441/1000000000000 : ℝ) (496070011721/500000000000 : ℝ) (496054444311/500000000000 : ℝ) (992108888623/1000000000000 : ℝ) (992124456031/1000000000000 : ℝ) (992124456033/1000000000000 : ℝ) (992124455909/1000000000000 : ℝ) (992124455911/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33229/262144 : ℝ)) 2 (992124456031/1000000000000 : ℝ) (992124456033/1000000000000 : ℝ) (992124455909/1000000000000 : ℝ) (992124455911/1000000000000 : ℝ) (99212445597/100000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33229/262144 : ℝ)) 3 (99212445597/100000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33229/262144 : ℝ)) 4 (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33229/262144 : ℝ)) 5 (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33229/262144 : ℝ)) 6 (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33229/262144 : ℝ)) 7 (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33229/262144 : ℝ))) (176614804889/1000000000000 : ℝ) (35322960979/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33229/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176614804889/1000000000000 : ℝ) (35322960979/200000000000 : ℝ) (147076850611/250000000000 : ℝ) (36769212653/62500000000 : ℝ) (6566494411/15625000000 : ℝ) (52531955289/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33229/262144 : ℝ))) 1 (147076850611/250000000000 : ℝ) (36769212653/62500000000 : ℝ) (6566494411/15625000000 : ℝ) (52531955289/125000000000 : ℝ) (252140761187/500000000000 : ℝ) (25214076119/50000000000 : ℝ) (49723184259/100000000000 : ℝ) (248615921299/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33229/262144 : ℝ))) 2 (252140761187/500000000000 : ℝ) (25214076119/50000000000 : ℝ) (49723184259/100000000000 : ℝ) (248615921299/500000000000 : ℝ) (250378341241/500000000000 : ℝ) (500756682489/1000000000000 : ℝ) (250372138303/500000000000 : ℝ) (250372138307/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33229/262144 : ℝ))) 3 (250378341241/500000000000 : ℝ) (500756682489/1000000000000 : ℝ) (250372138303/500000000000 : ℝ) (250372138307/500000000000 : ℝ) (62593809943/125000000000 : ℝ) (7824226243/15625000000 : ℝ) (100150095901/200000000000 : ℝ) (250375239757/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33229/262144 : ℝ))) 4 (62593809943/125000000000 : ℝ) (7824226243/15625000000 : ℝ) (100150095901/200000000000 : ℝ) (250375239757/500000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33229/262144 : ℝ))) 5 (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33229/262144 : ℝ))) 6 (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33229/262144 : ℝ))) 7 (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33229/262144 : ℝ)) hmem 8 (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33229/262144 : ℝ))) hcmem 8 (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33229/262144 : ℝ)) (992124455969/1000000000000 : ℝ) (248031113993/250000000000 : ℝ) (125187619881/250000000000 : ℝ) (500750479533/1000000000000 : ℝ) (396410454929/500000000000 : ℝ) (198205227469/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0448_exp_lower
  have heNumeric : (2054902110429/1000000000000 : ℝ)/4 ≤ Real.exp (-10657058386141/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902110429/1000000000000 : ℝ)/4 ≤ Real.exp ((8307/65536 : ℝ)-(198205227469/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8307/65536 : ℝ) (33229/262144 : ℝ) (198205227469/250000000000 : ℝ) (2054902110429/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0449; no trusted numerical premise.
theorem cover8_leaf0449_exp_radius : (998021297871388211/1000000000000000000 : ℝ) ≤ Real.exp ((-16615/1048576 : ℝ)/8) ∧ Real.exp ((-16615/1048576 : ℝ)/8) ≤ (249505324467847053/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16615/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0449_exp_lower : (920113477950436491/1000000000000000000 : ℝ) ≤ Real.exp ((-42628234724963/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628234724963/64000000000000 : ℝ)/8) ≤ (230028369487609123/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628234724963/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0449_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902072529/1000000000000 : ℝ) ≤ 4*Real.exp (33229/262144 : ℝ)*Real.exp (-mu (radius 8 (16615/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902072529/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16615/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0449_exp_radius
  have hrNumeric : (984279577541/1000000000000 : ℝ) ≤ Real.exp (-16615/1048576 : ℝ) ∧ Real.exp (-16615/1048576 : ℝ) ≤ (492139788771/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984279577541/1000000000000 : ℝ) ≤ (radius 8 (16615/131072 : ℝ)) ∧ (radius 8 (16615/131072 : ℝ)) ≤ (492139788771/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16615/131072 : ℝ)) (984279577541/1000000000000 : ℝ) (492139788771/500000000000 : ℝ) (176617420527/1000000000000 : ℝ) (176617420533/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16615/131072 : ℝ)) (984279577541/1000000000000 : ℝ) (492139788771/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16615/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984279577541/1000000000000 : ℝ) (492139788771/500000000000 : ℝ) (99213978877/100000000000 : ℝ) (992139788771/1000000000000 : ℝ) (248027163021/250000000000 : ℝ) (496054326043/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16615/131072 : ℝ)) 1 (99213978877/100000000000 : ℝ) (992139788771/1000000000000 : ℝ) (248027163021/250000000000 : ℝ) (496054326043/500000000000 : ℝ) (992124220427/1000000000000 : ℝ) (992124220429/1000000000000 : ℝ) (62007763769/62500000000 : ℝ) (992124220307/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16615/131072 : ℝ)) 2 (992124220427/1000000000000 : ℝ) (992124220429/1000000000000 : ℝ) (62007763769/62500000000 : ℝ) (992124220307/1000000000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16615/131072 : ℝ)) 3 (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16615/131072 : ℝ)) 4 (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16615/131072 : ℝ)) 5 (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16615/131072 : ℝ)) 6 (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16615/131072 : ℝ)) 7 (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16615/131072 : ℝ))) (176617420527/1000000000000 : ℝ) (176617420533/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16615/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (176617420527/1000000000000 : ℝ) (176617420533/1000000000000 : ℝ) (588308710263/1000000000000 : ℝ) (588308710267/1000000000000 : ℝ) (420258754253/1000000000000 : ℝ) (420258754261/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16615/131072 : ℝ))) 1 (588308710263/1000000000000 : ℝ) (588308710267/1000000000000 : ℝ) (420258754253/1000000000000 : ℝ) (420258754261/1000000000000 : ℝ) (252141866129/500000000000 : ℝ) (63035466533/125000000000 : ℝ) (248617118121/500000000000 : ℝ) (497234236249/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16615/131072 : ℝ))) 2 (252141866129/500000000000 : ℝ) (63035466533/125000000000 : ℝ) (248617118121/500000000000 : ℝ) (497234236249/1000000000000 : ℝ) (2003035937/4000000000 : ℝ) (500758984257/1000000000000 : ℝ) (250373289539/500000000000 : ℝ) (100149315817/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16615/131072 : ℝ))) 3 (2003035937/4000000000 : ℝ) (500758984257/1000000000000 : ℝ) (250373289539/500000000000 : ℝ) (100149315817/200000000000 : ℝ) (15648524427/31250000000 : ℝ) (500752781671/1000000000000 : ℝ) (4006022253/8000000000 : ℝ) (500752781633/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16615/131072 : ℝ))) 4 (15648524427/31250000000 : ℝ) (500752781671/1000000000000 : ℝ) (4006022253/8000000000 : ℝ) (500752781633/1000000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16615/131072 : ℝ))) 5 (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16615/131072 : ℝ))) 6 (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16615/131072 : ℝ))) 7 (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16615/131072 : ℝ)) hmem 8 (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16615/131072 : ℝ))) hcmem 8 (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16615/131072 : ℝ)) (198424844073/200000000000 : ℝ) (62007763773/62500000000 : ℝ) (125188195411/250000000000 : ℝ) (125188195413/250000000000 : ℝ) (792824743001/1000000000000 : ℝ) (792824743017/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0449_exp_lower
  have heNumeric : (2054902072529/1000000000000 : ℝ)/4 ≤ Real.exp (-42628234724963/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902072529/1000000000000 : ℝ)/4 ≤ Real.exp ((33229/262144 : ℝ)-(792824743017/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33229/262144 : ℝ) (16615/131072 : ℝ) (792824743017/1000000000000 : ℝ) (2054902072529/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0425_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0425_certificate
#check SmaleRate.Proofs.cover8_leaf0426_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0426_certificate
#check SmaleRate.Proofs.cover8_leaf0427_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0427_certificate
#check SmaleRate.Proofs.cover8_leaf0428_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0428_certificate
#check SmaleRate.Proofs.cover8_leaf0429_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0429_certificate
#check SmaleRate.Proofs.cover8_leaf0430_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0430_certificate
#check SmaleRate.Proofs.cover8_leaf0431_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0431_certificate
#check SmaleRate.Proofs.cover8_leaf0432_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0432_certificate
#check SmaleRate.Proofs.cover8_leaf0433_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0433_certificate
#check SmaleRate.Proofs.cover8_leaf0434_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0434_certificate
#check SmaleRate.Proofs.cover8_leaf0435_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0435_certificate
#check SmaleRate.Proofs.cover8_leaf0436_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0436_certificate
#check SmaleRate.Proofs.cover8_leaf0437_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0437_certificate
#check SmaleRate.Proofs.cover8_leaf0438_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0438_certificate
#check SmaleRate.Proofs.cover8_leaf0439_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0439_certificate
#check SmaleRate.Proofs.cover8_leaf0440_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0440_certificate
#check SmaleRate.Proofs.cover8_leaf0441_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0441_certificate
#check SmaleRate.Proofs.cover8_leaf0442_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0442_certificate
#check SmaleRate.Proofs.cover8_leaf0443_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0443_certificate
#check SmaleRate.Proofs.cover8_leaf0444_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0444_certificate
#check SmaleRate.Proofs.cover8_leaf0445_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0445_certificate
#check SmaleRate.Proofs.cover8_leaf0446_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0446_certificate
#check SmaleRate.Proofs.cover8_leaf0447_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0447_certificate
#check SmaleRate.Proofs.cover8_leaf0448_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0448_certificate
#check SmaleRate.Proofs.cover8_leaf0449_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0449_certificate
