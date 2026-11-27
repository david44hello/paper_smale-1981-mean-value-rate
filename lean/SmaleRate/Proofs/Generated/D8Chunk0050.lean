/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1250; no trusted numerical premise.
theorem cover8_leaf1250_exp_radius : (498997175378925597/500000000000000000 : ℝ) ≤ Real.exp ((-33683/2097152 : ℝ)/8) ∧ Real.exp ((-33683/2097152 : ℝ)/8) ≤ (199598870151570239/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33683/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1250_exp_lower : (920113435910145341/1000000000000000000 : ℝ) ≤ Real.exp ((-21314129059207/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314129059207/32000000000000 : ℝ)/8) ≤ (460056717955072671/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314129059207/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1250_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862665177/125000000000 : ℝ) ≤ 4*Real.exp (16841/131072 : ℝ)*Real.exp (-mu (radius 8 (33683/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (256862665177/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33683/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1250_exp_radius
  have hrNumeric : (196813397799/200000000000 : ℝ) ≤ Real.exp (-33683/2097152 : ℝ) ∧ Real.exp (-33683/2097152 : ℝ) ≤ (246016747249/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196813397799/200000000000 : ℝ) ≤ (radius 8 (33683/262144 : ℝ)) ∧ (radius 8 (33683/262144 : ℝ)) ≤ (246016747249/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33683/262144 : ℝ)) (196813397799/200000000000 : ℝ) (246016747249/250000000000 : ℝ) (88899045507/500000000000 : ℝ) (8889904551/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33683/262144 : ℝ)) (196813397799/200000000000 : ℝ) (246016747249/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33683/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196813397799/200000000000 : ℝ) (246016747249/250000000000 : ℝ) (992033494497/1000000000000 : ℝ) (496016747249/500000000000 : ℝ) (248000376637/250000000000 : ℝ) (19840030131/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33683/262144 : ℝ)) 1 (992033494497/1000000000000 : ℝ) (496016747249/500000000000 : ℝ) (248000376637/250000000000 : ℝ) (19840030131/20000000000 : ℝ) (496008750261/500000000000 : ℝ) (248004375131/250000000000 : ℝ) (992017500393/1000000000000 : ℝ) (248004375099/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33683/262144 : ℝ)) 2 (496008750261/500000000000 : ℝ) (248004375131/250000000000 : ℝ) (992017500393/1000000000000 : ℝ) (248004375099/250000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33683/262144 : ℝ)) 3 (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33683/262144 : ℝ)) 4 (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33683/262144 : ℝ)) 5 (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33683/262144 : ℝ)) 6 (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33683/262144 : ℝ)) 7 (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33683/262144 : ℝ))) (88899045507/500000000000 : ℝ) (8889904551/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33683/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88899045507/500000000000 : ℝ) (8889904551/50000000000 : ℝ) (588899045507/1000000000000 : ℝ) (58889904551/100000000000 : ℝ) (210830554601/500000000000 : ℝ) (42166110921/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33683/262144 : ℝ))) 1 (588899045507/1000000000000 : ℝ) (58889904551/100000000000 : ℝ) (210830554601/500000000000 : ℝ) (42166110921/100000000000 : ℝ) (252640038677/500000000000 : ℝ) (6316000967/12500000000 : ℝ) (99662595739/200000000000 : ℝ) (249156489351/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33683/262144 : ℝ))) 2 (252640038677/500000000000 : ℝ) (6316000967/12500000000 : ℝ) (99662595739/200000000000 : ℝ) (249156489351/500000000000 : ℝ) (62724566003/125000000000 : ℝ) (501796528031/1000000000000 : ℝ) (31361527263/62500000000 : ℝ) (62723054527/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33683/262144 : ℝ))) 3 (62724566003/125000000000 : ℝ) (501796528031/1000000000000 : ℝ) (31361527263/62500000000 : ℝ) (62723054527/125000000000 : ℝ) (125447620529/250000000000 : ℝ) (125447620531/250000000000 : ℝ) (501790482079/1000000000000 : ℝ) (62723810261/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33683/262144 : ℝ))) 4 (125447620529/250000000000 : ℝ) (125447620531/250000000000 : ℝ) (501790482079/1000000000000 : ℝ) (62723810261/125000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33683/262144 : ℝ))) 5 (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33683/262144 : ℝ))) 6 (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33683/262144 : ℝ))) 7 (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33683/262144 : ℝ)) hmem 8 (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33683/262144 : ℝ))) hcmem 8 (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33683/262144 : ℝ)) (992017500457/1000000000000 : ℝ) (49600875023/50000000000 : ℝ) (501790482097/1000000000000 : ℝ) (250895241053/500000000000 : ℝ) (794553166383/1000000000000 : ℝ) (794553166401/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1250_exp_lower
  have heNumeric : (256862665177/125000000000 : ℝ)/4 ≤ Real.exp (-21314129059207/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862665177/125000000000 : ℝ)/4 ≤ Real.exp ((16841/131072 : ℝ)-(794553166401/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16841/131072 : ℝ) (33683/262144 : ℝ) (794553166401/1000000000000 : ℝ) (256862665177/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1251; no trusted numerical premise.
theorem cover8_leaf1251_exp_radius : (498997145636377101/500000000000000000 : ℝ) ≤ Real.exp ((-8421/524288 : ℝ)/8) ∧ Real.exp ((-8421/524288 : ℝ)/8) ≤ (997994291272754203/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8421/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1251_exp_lower : (920113437828727421/1000000000000000000 : ℝ) ≤ Real.exp ((-42628257050813/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628257050813/64000000000000 : ℝ)/8) ≤ (460056718914363711/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628257050813/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1251_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450677847/500000000000 : ℝ) ≤ 4*Real.exp (33683/262144 : ℝ)*Real.exp (-mu (radius 8 (8421/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450677847/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8421/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1251_exp_radius
  have hrNumeric : (196813303951/200000000000 : ℝ) ≤ Real.exp (-8421/524288 : ℝ) ∧ Real.exp (-8421/524288 : ℝ) ≤ (246016629939/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196813303951/200000000000 : ℝ) ≤ (radius 8 (8421/65536 : ℝ)) ∧ (radius 8 (8421/65536 : ℝ)) ≤ (246016629939/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8421/65536 : ℝ)) (196813303951/200000000000 : ℝ) (246016629939/250000000000 : ℝ) (88900344059/500000000000 : ℝ) (44450172031/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8421/65536 : ℝ)) (196813303951/200000000000 : ℝ) (246016629939/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8421/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196813303951/200000000000 : ℝ) (246016629939/250000000000 : ℝ) (992033259877/1000000000000 : ℝ) (496016629939/500000000000 : ℝ) (248000317509/250000000000 : ℝ) (496000635019/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8421/65536 : ℝ)) 1 (992033259877/1000000000000 : ℝ) (496016629939/500000000000 : ℝ) (248000317509/250000000000 : ℝ) (496000635019/500000000000 : ℝ) (248004316239/250000000000 : ℝ) (496008632479/500000000000 : ℝ) (992017264827/1000000000000 : ℝ) (99201726483/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8421/65536 : ℝ)) 2 (248004316239/250000000000 : ℝ) (496008632479/500000000000 : ℝ) (992017264827/1000000000000 : ℝ) (99201726483/100000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8421/65536 : ℝ)) 3 (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8421/65536 : ℝ)) 4 (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8421/65536 : ℝ)) 5 (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8421/65536 : ℝ)) 6 (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8421/65536 : ℝ)) 7 (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8421/65536 : ℝ))) (88900344059/500000000000 : ℝ) (44450172031/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8421/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88900344059/500000000000 : ℝ) (44450172031/250000000000 : ℝ) (588900344059/1000000000000 : ℝ) (294450172031/500000000000 : ℝ) (421664188801/1000000000000 : ℝ) (42166418881/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8421/65536 : ℝ))) 1 (588900344059/1000000000000 : ℝ) (294450172031/500000000000 : ℝ) (421664188801/1000000000000 : ℝ) (42166418881/100000000000 : ℝ) (50528226643/100000000000 : ℝ) (126320566609/250000000000 : ℝ) (498315347809/1000000000000 : ℝ) (62289418477/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8421/65536 : ℝ))) 2 (50528226643/100000000000 : ℝ) (126320566609/250000000000 : ℝ) (498315347809/1000000000000 : ℝ) (62289418477/125000000000 : ℝ) (501798807119/1000000000000 : ℝ) (250899403563/500000000000 : ℝ) (501786715983/1000000000000 : ℝ) (501786715991/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8421/65536 : ℝ))) 3 (501798807119/1000000000000 : ℝ) (250899403563/500000000000 : ℝ) (501786715983/1000000000000 : ℝ) (501786715991/1000000000000 : ℝ) (501792761551/1000000000000 : ℝ) (501792761559/1000000000000 : ℝ) (250896380757/500000000000 : ℝ) (501792761523/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8421/65536 : ℝ))) 4 (501792761551/1000000000000 : ℝ) (501792761559/1000000000000 : ℝ) (250896380757/500000000000 : ℝ) (501792761523/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8421/65536 : ℝ))) 5 (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8421/65536 : ℝ))) 6 (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8421/65536 : ℝ))) 7 (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8421/65536 : ℝ)) hmem 8 (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8421/65536 : ℝ))) hcmem 8 (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8421/65536 : ℝ)) (992017264891/1000000000000 : ℝ) (496008632447/500000000000 : ℝ) (125448190383/250000000000 : ℝ) (501792761541/1000000000000 : ℝ) (1986392411/2500000000 : ℝ) (794556964417/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1251_exp_lower
  have heNumeric : (1027450677847/500000000000 : ℝ)/4 ≤ Real.exp (-42628257050813/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450677847/500000000000 : ℝ)/4 ≤ Real.exp ((33683/262144 : ℝ)-(794556964417/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33683/262144 : ℝ) (8421/65536 : ℝ) (794556964417/1000000000000 : ℝ) (1027450677847/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1252; no trusted numerical premise.
theorem cover8_leaf1252_exp_radius : (249498557946915189/250000000000000000 : ℝ) ≤ Real.exp ((-33685/2097152 : ℝ)/8) ∧ Real.exp ((-33685/2097152 : ℝ)/8) ≤ (997994231787660757/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33685/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1252_exp_lower : (920113439756740669/1000000000000000000 : ℝ) ≤ Real.exp ((-10657063994491/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657063994491/16000000000000 : ℝ)/8) ≤ (92011343975674067/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657063994491/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1252_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901390141/1000000000000 : ℝ) ≤ 4*Real.exp (8421/65536 : ℝ)*Real.exp (-mu (radius 8 (33685/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901390141/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33685/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1252_exp_radius
  have hrNumeric : (246016512629/250000000000 : ℝ) ≤ Real.exp (-33685/2097152 : ℝ) ∧ Real.exp (-33685/2097152 : ℝ) ≤ (984066050517/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246016512629/250000000000 : ℝ) ≤ (radius 8 (33685/262144 : ℝ)) ∧ (radius 8 (33685/262144 : ℝ)) ≤ (984066050517/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33685/262144 : ℝ)) (246016512629/250000000000 : ℝ) (984066050517/1000000000000 : ℝ) (177803285177/1000000000000 : ℝ) (177803285183/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33685/262144 : ℝ)) (246016512629/250000000000 : ℝ) (984066050517/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33685/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246016512629/250000000000 : ℝ) (984066050517/1000000000000 : ℝ) (496016512629/500000000000 : ℝ) (992033025259/1000000000000 : ℝ) (39680041341/40000000000 : ℝ) (992001033527/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33685/262144 : ℝ)) 1 (496016512629/500000000000 : ℝ) (992033025259/1000000000000 : ℝ) (39680041341/40000000000 : ℝ) (992001033527/1000000000000 : ℝ) (992017029391/1000000000000 : ℝ) (992017029393/1000000000000 : ℝ) (496008514631/500000000000 : ℝ) (198403405853/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33685/262144 : ℝ)) 2 (992017029391/1000000000000 : ℝ) (992017029393/1000000000000 : ℝ) (496008514631/500000000000 : ℝ) (198403405853/200000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33685/262144 : ℝ)) 3 (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33685/262144 : ℝ)) 4 (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33685/262144 : ℝ)) 5 (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33685/262144 : ℝ)) 6 (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33685/262144 : ℝ)) 7 (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33685/262144 : ℝ))) (177803285177/1000000000000 : ℝ) (177803285183/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33685/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177803285177/1000000000000 : ℝ) (177803285183/1000000000000 : ℝ) (147225410647/250000000000 : ℝ) (18403176331/31250000000 : ℝ) (16866690733/40000000000 : ℝ) (421667268333/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33685/262144 : ℝ))) 1 (147225410647/250000000000 : ℝ) (18403176331/31250000000 : ℝ) (16866690733/40000000000 : ℝ) (421667268333/1000000000000 : ℝ) (15790139233/31250000000 : ℝ) (505284455463/1000000000000 : ℝ) (99663543373/200000000000 : ℝ) (498317716873/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33685/262144 : ℝ))) 2 (15790139233/31250000000 : ℝ) (505284455463/1000000000000 : ℝ) (99663543373/200000000000 : ℝ) (498317716873/1000000000000 : ℝ) (6272513577/12500000000 : ℝ) (62725135771/125000000000 : ℝ) (62723624463/125000000000 : ℝ) (501788995713/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33685/262144 : ℝ))) 3 (6272513577/12500000000 : ℝ) (62725135771/125000000000 : ℝ) (62723624463/125000000000 : ℝ) (501788995713/1000000000000 : ℝ) (125448760233/250000000000 : ℝ) (501795040941/1000000000000 : ℝ) (100359008179/200000000000 : ℝ) (100359008181/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33685/262144 : ℝ))) 4 (125448760233/250000000000 : ℝ) (501795040941/1000000000000 : ℝ) (100359008179/200000000000 : ℝ) (100359008181/200000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33685/262144 : ℝ))) 5 (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33685/262144 : ℝ))) 6 (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33685/262144 : ℝ))) 7 (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33685/262144 : ℝ)) hmem 8 (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33685/262144 : ℝ))) hcmem 8 (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33685/262144 : ℝ)) (496008514663/500000000000 : ℝ) (992017029329/1000000000000 : ℝ) (501795040913/1000000000000 : ℝ) (501795040923/1000000000000 : ℝ) (198640190583/250000000000 : ℝ) (794560762351/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1252_exp_lower
  have heNumeric : (2054901390141/1000000000000 : ℝ)/4 ≤ Real.exp (-10657063994491/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901390141/1000000000000 : ℝ)/4 ≤ Real.exp ((8421/65536 : ℝ)-(794560762351/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8421/65536 : ℝ) (33685/262144 : ℝ) (794560762351/1000000000000 : ℝ) (2054901390141/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1253; no trusted numerical premise.
theorem cover8_leaf1253_exp_radius : (199598834460514171/200000000000000000 : ℝ) ≤ Real.exp ((-16843/1048576 : ℝ)/8) ∧ Real.exp ((-16843/1048576 : ℝ)/8) ≤ (124749271537821357/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16843/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1253_exp_lower : (460056720846862513/500000000000000000 : ℝ) ≤ Real.exp ((-42628254900123/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628254900123/64000000000000 : ℝ)/8) ≤ (920113441693725027/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628254900123/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1253_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725356187/250000000000 : ℝ) ≤ 4*Real.exp (33685/262144 : ℝ)*Real.exp (-mu (radius 8 (16843/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513725356187/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16843/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1253_exp_radius
  have hrNumeric : (984065581277/1000000000000 : ℝ) ≤ Real.exp (-16843/1048576 : ℝ) ∧ Real.exp (-16843/1048576 : ℝ) ≤ (492032790639/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984065581277/1000000000000 : ℝ) ≤ (radius 8 (16843/131072 : ℝ)) ∧ (radius 8 (16843/131072 : ℝ)) ≤ (492032790639/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16843/131072 : ℝ)) (984065581277/1000000000000 : ℝ) (492032790639/500000000000 : ℝ) (177805882197/1000000000000 : ℝ) (177805882203/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16843/131072 : ℝ)) (984065581277/1000000000000 : ℝ) (492032790639/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16843/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984065581277/1000000000000 : ℝ) (492032790639/500000000000 : ℝ) (496016395319/500000000000 : ℝ) (992032790639/1000000000000 : ℝ) (496000398507/500000000000 : ℝ) (198400159403/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16843/131072 : ℝ)) 1 (496016395319/500000000000 : ℝ) (992032790639/1000000000000 : ℝ) (496000398507/500000000000 : ℝ) (198400159403/200000000000 : ℝ) (496008396913/500000000000 : ℝ) (992016793827/1000000000000 : ℝ) (992016793697/1000000000000 : ℝ) (992016793699/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16843/131072 : ℝ)) 2 (496008396913/500000000000 : ℝ) (992016793827/1000000000000 : ℝ) (992016793697/1000000000000 : ℝ) (992016793699/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16843/131072 : ℝ)) 3 (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16843/131072 : ℝ)) 4 (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16843/131072 : ℝ)) 5 (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16843/131072 : ℝ)) 6 (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16843/131072 : ℝ)) 7 (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16843/131072 : ℝ))) (177805882197/1000000000000 : ℝ) (177805882203/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16843/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177805882197/1000000000000 : ℝ) (177805882203/1000000000000 : ℝ) (294451470549/500000000000 : ℝ) (294451470551/500000000000 : ℝ) (21083517389/50000000000 : ℝ) (105417586947/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16843/131072 : ℝ))) 1 (294451470549/500000000000 : ℝ) (294451470551/500000000000 : ℝ) (21083517389/50000000000 : ℝ) (105417586947/250000000000 : ℝ) (505286644439/1000000000000 : ℝ) (101057328889/200000000000 : ℝ) (498320085869/1000000000000 : ℝ) (498320085877/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16843/131072 : ℝ))) 2 (505286644439/1000000000000 : ℝ) (101057328889/200000000000 : ℝ) (498320085869/1000000000000 : ℝ) (498320085877/1000000000000 : ℝ) (250901682577/500000000000 : ℝ) (501803365161/1000000000000 : ℝ) (501791275377/1000000000000 : ℝ) (100358255077/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16843/131072 : ℝ))) 3 (250901682577/500000000000 : ℝ) (501803365161/1000000000000 : ℝ) (501791275377/1000000000000 : ℝ) (100358255077/200000000000 : ℝ) (100359464053/200000000000 : ℝ) (501797320273/1000000000000 : ℝ) (501797320229/1000000000000 : ℝ) (501797320237/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16843/131072 : ℝ))) 4 (100359464053/200000000000 : ℝ) (501797320273/1000000000000 : ℝ) (501797320229/1000000000000 : ℝ) (501797320237/1000000000000 : ℝ) (501797320247/1000000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16843/131072 : ℝ))) 5 (501797320247/1000000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16843/131072 : ℝ))) 6 (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16843/131072 : ℝ))) 7 (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16843/131072 : ℝ)) hmem 8 (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16843/131072 : ℝ))) hcmem 8 (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16843/131072 : ℝ)) (992016793761/1000000000000 : ℝ) (992016793763/1000000000000 : ℝ) (250898660123/500000000000 : ℝ) (100359464051/200000000000 : ℝ) (79456456019/100000000000 : ℝ) (794564560207/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1253_exp_lower
  have heNumeric : (513725356187/250000000000 : ℝ)/4 ≤ Real.exp (-42628254900123/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725356187/250000000000 : ℝ)/4 ≤ Real.exp ((33685/262144 : ℝ)-(794564560207/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33685/262144 : ℝ) (16843/131072 : ℝ) (794564560207/1000000000000 : ℝ) (513725356187/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1254; no trusted numerical premise.
theorem cover8_leaf1254_exp_radius : (1995988225634969/2000000000000000 : ℝ) ≤ Real.exp ((-33687/2097152 : ℝ)/8) ∧ Real.exp ((-33687/2097152 : ℝ)/8) ≤ (997994112817484501/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33687/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1254_exp_lower : (920113443638990409/1000000000000000000 : ℝ) ≤ Real.exp ((-21314126908837/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314126908837/32000000000000 : ℝ)/8) ≤ (92011344363899041/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314126908837/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1254_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901459503/1000000000000 : ℝ) ≤ 4*Real.exp (16843/131072 : ℝ)*Real.exp (-mu (radius 8 (33687/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901459503/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33687/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1254_exp_radius
  have hrNumeric : (492032556019/500000000000 : ℝ) ≤ Real.exp (-33687/2097152 : ℝ) ∧ Real.exp (-33687/2097152 : ℝ) ≤ (984065112039/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492032556019/500000000000 : ℝ) ≤ (radius 8 (33687/262144 : ℝ)) ∧ (radius 8 (33687/262144 : ℝ)) ≤ (984065112039/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33687/262144 : ℝ)) (492032556019/500000000000 : ℝ) (984065112039/1000000000000 : ℝ) (88904239589/500000000000 : ℝ) (11113029949/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33687/262144 : ℝ)) (492032556019/500000000000 : ℝ) (984065112039/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33687/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492032556019/500000000000 : ℝ) (984065112039/1000000000000 : ℝ) (992032556019/1000000000000 : ℝ) (49601627801/50000000000 : ℝ) (496000280251/500000000000 : ℝ) (124000070063/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33687/262144 : ℝ)) 1 (992032556019/1000000000000 : ℝ) (49601627801/50000000000 : ℝ) (496000280251/500000000000 : ℝ) (124000070063/125000000000 : ℝ) (49600827913/50000000000 : ℝ) (496008279131/500000000000 : ℝ) (992016558131/1000000000000 : ℝ) (496008279067/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33687/262144 : ℝ)) 2 (49600827913/50000000000 : ℝ) (496008279131/500000000000 : ℝ) (992016558131/1000000000000 : ℝ) (496008279067/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33687/262144 : ℝ)) 3 (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33687/262144 : ℝ)) 4 (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33687/262144 : ℝ)) 5 (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33687/262144 : ℝ)) 6 (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33687/262144 : ℝ)) 7 (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33687/262144 : ℝ))) (88904239589/500000000000 : ℝ) (11113029949/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33687/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88904239589/500000000000 : ℝ) (11113029949/62500000000 : ℝ) (588904239589/1000000000000 : ℝ) (73613029949/125000000000 : ℝ) (210836713583/500000000000 : ℝ) (210836713587/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33687/262144 : ℝ))) 1 (588904239589/1000000000000 : ℝ) (73613029949/125000000000 : ℝ) (210836713583/500000000000 : ℝ) (210836713587/500000000000 : ℝ) (505288833377/1000000000000 : ℝ) (505288833383/1000000000000 : ℝ) (249161227411/500000000000 : ℝ) (498322454829/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33687/262144 : ℝ))) 2 (505288833377/1000000000000 : ℝ) (505288833383/1000000000000 : ℝ) (249161227411/500000000000 : ℝ) (498322454829/1000000000000 : ℝ) (501805644099/1000000000000 : ℝ) (250902822053/500000000000 : ℝ) (501793555003/1000000000000 : ℝ) (50179355501/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33687/262144 : ℝ))) 3 (501805644099/1000000000000 : ℝ) (250902822053/500000000000 : ℝ) (501793555003/1000000000000 : ℝ) (50179355501/100000000000 : ℝ) (501799599551/1000000000000 : ℝ) (250899799779/500000000000 : ℝ) (250899799757/500000000000 : ℝ) (250899799761/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33687/262144 : ℝ))) 4 (501799599551/1000000000000 : ℝ) (250899799779/500000000000 : ℝ) (250899799757/500000000000 : ℝ) (250899799761/500000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33687/262144 : ℝ))) 5 (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33687/262144 : ℝ))) 6 (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33687/262144 : ℝ))) 7 (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33687/262144 : ℝ)) hmem 8 (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33687/262144 : ℝ))) hcmem 8 (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33687/262144 : ℝ)) (198403311639/200000000000 : ℝ) (496008279099/500000000000 : ℝ) (125449899883/250000000000 : ℝ) (25089979977/50000000000 : ℝ) (31782734319/40000000000 : ℝ) (794568357991/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1254_exp_lower
  have heNumeric : (2054901459503/1000000000000 : ℝ)/4 ≤ Real.exp (-21314126908837/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901459503/1000000000000 : ℝ)/4 ≤ Real.exp ((16843/131072 : ℝ)-(794568357991/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16843/131072 : ℝ) (33687/262144 : ℝ) (794568357991/1000000000000 : ℝ) (2054901459503/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1255; no trusted numerical premise.
theorem cover8_leaf1255_exp_radius : (99799405333240169/100000000000000000 : ℝ) ≤ Real.exp ((-4211/262144 : ℝ)/8) ∧ Real.exp ((-4211/262144 : ℝ)/8) ≤ (997994053332401691/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4211/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1255_exp_lower : (184022689118553369/200000000000000000 : ℝ) ≤ Real.exp ((-42628252730489/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628252730489/64000000000000 : ℝ)/8) ≤ (460056722796383423/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628252730489/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1255_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490149441/100000000000 : ℝ) ≤ 4*Real.exp (33687/262144 : ℝ)*Real.exp (-mu (radius 8 (4211/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (205490149441/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4211/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1255_exp_radius
  have hrNumeric : (984064642799/1000000000000 : ℝ) ≤ Real.exp (-4211/262144 : ℝ) ∧ Real.exp (-4211/262144 : ℝ) ≤ (2460161607/2500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984064642799/1000000000000 : ℝ) ≤ (radius 8 (4211/32768 : ℝ)) ∧ (radius 8 (4211/32768 : ℝ)) ≤ (2460161607/2500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4211/32768 : ℝ)) (984064642799/1000000000000 : ℝ) (2460161607/2500000000 : ℝ) (177811076119/1000000000000 : ℝ) (88905538063/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4211/32768 : ℝ)) (984064642799/1000000000000 : ℝ) (2460161607/2500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4211/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984064642799/1000000000000 : ℝ) (2460161607/2500000000 : ℝ) (992032321399/1000000000000 : ℝ) (4960161607/5000000000 : ℝ) (992000323991/1000000000000 : ℝ) (124000040499/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4211/32768 : ℝ)) 1 (992032321399/1000000000000 : ℝ) (4960161607/5000000000 : ℝ) (992000323991/1000000000000 : ℝ) (124000040499/125000000000 : ℝ) (198403264539/200000000000 : ℝ) (124002040337/125000000000 : ℝ) (198403264513/200000000000 : ℝ) (992016322567/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4211/32768 : ℝ)) 2 (198403264539/200000000000 : ℝ) (124002040337/125000000000 : ℝ) (198403264513/200000000000 : ℝ) (992016322567/1000000000000 : ℝ) (99201632263/100000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4211/32768 : ℝ)) 3 (99201632263/100000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4211/32768 : ℝ)) 4 (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4211/32768 : ℝ)) 5 (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4211/32768 : ℝ)) 6 (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4211/32768 : ℝ)) 7 (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4211/32768 : ℝ))) (177811076119/1000000000000 : ℝ) (88905538063/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4211/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177811076119/1000000000000 : ℝ) (88905538063/500000000000 : ℝ) (588905538059/1000000000000 : ℝ) (588905538063/1000000000000 : ℝ) (210838253241/500000000000 : ℝ) (421676506491/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4211/32768 : ℝ))) 1 (588905538059/1000000000000 : ℝ) (588905538063/1000000000000 : ℝ) (210838253241/500000000000 : ℝ) (421676506491/1000000000000 : ℝ) (50529102227/100000000000 : ℝ) (505291022277/1000000000000 : ℝ) (498324823721/1000000000000 : ℝ) (498324823729/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4211/32768 : ℝ))) 2 (50529102227/100000000000 : ℝ) (505291022277/1000000000000 : ℝ) (498324823721/1000000000000 : ℝ) (498324823729/1000000000000 : ℝ) (100361584599/200000000000 : ℝ) (501807923003/1000000000000 : ℝ) (250897917289/500000000000 : ℝ) (501795834587/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4211/32768 : ℝ))) 3 (100361584599/200000000000 : ℝ) (501807923003/1000000000000 : ℝ) (250897917289/500000000000 : ℝ) (501795834587/1000000000000 : ℝ) (250900939393/500000000000 : ℝ) (100360375759/200000000000 : ℝ) (401441503/800000000 : ℝ) (501801878759/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4211/32768 : ℝ))) 4 (250900939393/500000000000 : ℝ) (100360375759/200000000000 : ℝ) (401441503/800000000 : ℝ) (501801878759/1000000000000 : ℝ) (31362617423/62500000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4211/32768 : ℝ))) 5 (31362617423/62500000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4211/32768 : ℝ))) 6 (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4211/32768 : ℝ))) 7 (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4211/32768 : ℝ)) hmem 8 (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4211/32768 : ℝ))) hcmem 8 (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4211/32768 : ℝ)) (992016322629/1000000000000 : ℝ) (124002040329/125000000000 : ℝ) (501801878767/1000000000000 : ℝ) (501801878777/1000000000000 : ℝ) (397286077841/500000000000 : ℝ) (794572155701/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1255_exp_lower
  have heNumeric : (205490149441/100000000000 : ℝ)/4 ≤ Real.exp (-42628252730489/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490149441/100000000000 : ℝ)/4 ≤ Real.exp ((33687/262144 : ℝ)-(794572155701/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33687/262144 : ℝ) (4211/32768 : ℝ) (794572155701/1000000000000 : ℝ) (205490149441/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1256; no trusted numerical premise.
theorem cover8_leaf1256_exp_radius : (498996996923661213/500000000000000000 : ℝ) ≤ Real.exp ((-33689/2097152 : ℝ)/8) ∧ Real.exp ((-33689/2097152 : ℝ)/8) ≤ (997993993847322427/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33689/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1256_exp_lower : (460056723778044731/500000000000000000 : ℝ) ≤ Real.exp ((-5328531454749/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328531454749/8000000000000 : ℝ)/8) ≤ (920113447556089463/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328531454749/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1256_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431345593/62500000000 : ℝ) ≤ 4*Real.exp (4211/32768 : ℝ)*Real.exp (-mu (radius 8 (33689/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (128431345593/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33689/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1256_exp_radius
  have hrNumeric : (984064173561/1000000000000 : ℝ) ≤ Real.exp (-33689/2097152 : ℝ) ∧ Real.exp (-33689/2097152 : ℝ) ≤ (492032086781/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984064173561/1000000000000 : ℝ) ≤ (radius 8 (33689/262144 : ℝ)) ∧ (radius 8 (33689/262144 : ℝ)) ≤ (492032086781/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33689/262144 : ℝ)) (984064173561/1000000000000 : ℝ) (492032086781/500000000000 : ℝ) (22226709127/125000000000 : ℝ) (177813673023/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33689/262144 : ℝ)) (984064173561/1000000000000 : ℝ) (492032086781/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33689/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984064173561/1000000000000 : ℝ) (492032086781/500000000000 : ℝ) (49601604339/50000000000 : ℝ) (992032086781/1000000000000 : ℝ) (24800002187/25000000000 : ℝ) (992000087481/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33689/262144 : ℝ)) 1 (49601604339/50000000000 : ℝ) (992032086781/1000000000000 : ℝ) (24800002187/25000000000 : ℝ) (992000087481/1000000000000 : ℝ) (99201608713/100000000000 : ℝ) (992016087131/1000000000000 : ℝ) (992016087/1000000000 : ℝ) (496008043501/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33689/262144 : ℝ)) 2 (99201608713/100000000000 : ℝ) (992016087131/1000000000000 : ℝ) (992016087/1000000000 : ℝ) (496008043501/500000000000 : ℝ) (198403217413/200000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33689/262144 : ℝ)) 3 (198403217413/200000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33689/262144 : ℝ)) 4 (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33689/262144 : ℝ)) 5 (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33689/262144 : ℝ)) 6 (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33689/262144 : ℝ)) 7 (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33689/262144 : ℝ))) (22226709127/125000000000 : ℝ) (177813673023/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33689/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22226709127/125000000000 : ℝ) (177813673023/1000000000000 : ℝ) (147226709127/250000000000 : ℝ) (18403338641/31250000000 : ℝ) (421679585723/1000000000000 : ℝ) (105419896433/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33689/262144 : ℝ))) 1 (147226709127/250000000000 : ℝ) (18403338641/31250000000 : ℝ) (421679585723/1000000000000 : ℝ) (105419896433/250000000000 : ℝ) (101058642223/200000000000 : ℝ) (252646605561/500000000000 : ℝ) (498327192563/1000000000000 : ℝ) (498327192571/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33689/262144 : ℝ))) 2 (101058642223/200000000000 : ℝ) (252646605561/500000000000 : ℝ) (498327192563/1000000000000 : ℝ) (498327192571/1000000000000 : ℝ) (501810201839/1000000000000 : ℝ) (501810201847/1000000000000 : ℝ) (501798114101/1000000000000 : ℝ) (50179811411/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33689/262144 : ℝ))) 3 (501810201839/1000000000000 : ℝ) (501810201847/1000000000000 : ℝ) (501798114101/1000000000000 : ℝ) (50179811411/100000000000 : ℝ) (50180415797/100000000000 : ℝ) (501804157979/1000000000000 : ℝ) (501804157933/1000000000000 : ℝ) (501804157943/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33689/262144 : ℝ))) 4 (50180415797/100000000000 : ℝ) (501804157979/1000000000000 : ℝ) (501804157933/1000000000000 : ℝ) (501804157943/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33689/262144 : ℝ))) 5 (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33689/262144 : ℝ))) 6 (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33689/262144 : ℝ))) 7 (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33689/262144 : ℝ)) hmem 8 (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33689/262144 : ℝ))) hcmem 8 (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33689/262144 : ℝ)) (124002010883/125000000000 : ℝ) (992016087067/1000000000000 : ℝ) (501804157951/1000000000000 : ℝ) (501804157961/1000000000000 : ℝ) (794575953309/1000000000000 : ℝ) (49660997083/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1256_exp_lower
  have heNumeric : (128431345593/62500000000 : ℝ)/4 ≤ Real.exp (-5328531454749/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431345593/62500000000 : ℝ)/4 ≤ Real.exp ((4211/32768 : ℝ)-(49660997083/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4211/32768 : ℝ) (33689/262144 : ℝ) (49660997083/62500000000 : ℝ) (128431345593/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1257; no trusted numerical premise.
theorem cover8_leaf1257_exp_radius : (997993934362246707/1000000000000000000 : ℝ) ≤ Real.exp ((-16845/1048576 : ℝ)/8) ∧ Real.exp ((-16845/1048576 : ℝ)/8) ≤ (249498483590561677/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16845/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1257_exp_lower : (460056724763674031/500000000000000000 : ℝ) ≤ Real.exp ((-42628250541079/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628250541079/64000000000000 : ℝ)/8) ≤ (920113449527348063/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628250541079/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1257_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901564707/1000000000000 : ℝ) ≤ 4*Real.exp (33689/262144 : ℝ)*Real.exp (-mu (radius 8 (16845/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901564707/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16845/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1257_exp_radius
  have hrNumeric : (492031852161/500000000000 : ℝ) ≤ Real.exp (-16845/1048576 : ℝ) ∧ Real.exp (-16845/1048576 : ℝ) ≤ (984063704323/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492031852161/500000000000 : ℝ) ≤ (radius 8 (16845/131072 : ℝ)) ∧ (radius 8 (16845/131072 : ℝ)) ≤ (984063704323/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16845/131072 : ℝ)) (492031852161/500000000000 : ℝ) (984063704323/1000000000000 : ℝ) (4445406747/25000000000 : ℝ) (88908134943/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16845/131072 : ℝ)) (492031852161/500000000000 : ℝ) (984063704323/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16845/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492031852161/500000000000 : ℝ) (984063704323/1000000000000 : ℝ) (992031852161/1000000000000 : ℝ) (496015926081/500000000000 : ℝ) (123999981371/125000000000 : ℝ) (99199985097/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16845/131072 : ℝ)) 1 (992031852161/1000000000000 : ℝ) (496015926081/500000000000 : ℝ) (123999981371/125000000000 : ℝ) (99199985097/100000000000 : ℝ) (248003962891/250000000000 : ℝ) (496007925783/500000000000 : ℝ) (198403170287/200000000000 : ℝ) (992015851437/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16845/131072 : ℝ)) 2 (248003962891/250000000000 : ℝ) (496007925783/500000000000 : ℝ) (198403170287/200000000000 : ℝ) (992015851437/1000000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16845/131072 : ℝ)) 3 (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16845/131072 : ℝ)) 4 (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16845/131072 : ℝ)) 5 (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16845/131072 : ℝ)) 6 (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16845/131072 : ℝ)) 7 (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16845/131072 : ℝ))) (4445406747/25000000000 : ℝ) (88908134943/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16845/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4445406747/25000000000 : ℝ) (88908134943/500000000000 : ℝ) (29445406747/50000000000 : ℝ) (588908134943/1000000000000 : ℝ) (421682664903/1000000000000 : ℝ) (421682664911/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16845/131072 : ℝ))) 1 (29445406747/50000000000 : ℝ) (588908134943/1000000000000 : ℝ) (421682664903/1000000000000 : ℝ) (421682664911/1000000000000 : ℝ) (505295399921/1000000000000 : ℝ) (505295399927/1000000000000 : ℝ) (498329561359/1000000000000 : ℝ) (249164780683/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16845/131072 : ℝ))) 2 (505295399921/1000000000000 : ℝ) (505295399927/1000000000000 : ℝ) (498329561359/1000000000000 : ℝ) (249164780683/500000000000 : ℝ) (784082001/1562500000 : ℝ) (501812480647/1000000000000 : ℝ) (250900196791/500000000000 : ℝ) (501800393589/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16845/131072 : ℝ))) 3 (784082001/1562500000 : ℝ) (501812480647/1000000000000 : ℝ) (250900196791/500000000000 : ℝ) (501800393589/1000000000000 : ℝ) (501806437111/1000000000000 : ℝ) (250903218559/500000000000 : ℝ) (250903218537/500000000000 : ℝ) (250903218541/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16845/131072 : ℝ))) 4 (501806437111/1000000000000 : ℝ) (250903218559/500000000000 : ℝ) (250903218537/500000000000 : ℝ) (250903218541/500000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16845/131072 : ℝ))) 5 (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16845/131072 : ℝ))) 6 (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16845/131072 : ℝ))) 7 (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16845/131072 : ℝ)) hmem 8 (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16845/131072 : ℝ))) hcmem 8 (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16845/131072 : ℝ)) (992015851499/1000000000000 : ℝ) (496007925751/500000000000 : ℝ) (125451609273/250000000000 : ℝ) (5018064371/10000000000 : ℝ) (79457975087/100000000000 : ℝ) (397289875443/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1257_exp_lower
  have heNumeric : (2054901564707/1000000000000 : ℝ)/4 ≤ Real.exp (-42628250541079/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901564707/1000000000000 : ℝ)/4 ≤ Real.exp ((33689/262144 : ℝ)-(397289875443/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33689/262144 : ℝ) (16845/131072 : ℝ) (397289875443/500000000000 : ℝ) (2054901564707/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1258; no trusted numerical premise.
theorem cover8_leaf1258_exp_radius : (199598774975434907/200000000000000000 : ℝ) ≤ Real.exp ((-33691/2097152 : ℝ)/8) ∧ Real.exp ((-33691/2097152 : ℝ)/8) ≤ (124749234359646817/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33691/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1258_exp_lower : (184022690301584563/200000000000000000 : ℝ) ≤ Real.exp ((-21314124719491/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314124719491/32000000000000 : ℝ)/8) ≤ (7188386339905647/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314124719491/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1258_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901600093/1000000000000 : ℝ) ≤ 4*Real.exp (16845/131072 : ℝ)*Real.exp (-mu (radius 8 (33691/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901600093/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33691/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1258_exp_radius
  have hrNumeric : (246015808771/250000000000 : ℝ) ≤ Real.exp (-33691/2097152 : ℝ) ∧ Real.exp (-33691/2097152 : ℝ) ≤ (196812647017/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246015808771/250000000000 : ℝ) ≤ (radius 8 (33691/262144 : ℝ)) ∧ (radius 8 (33691/262144 : ℝ)) ≤ (196812647017/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33691/262144 : ℝ)) (246015808771/250000000000 : ℝ) (196812647017/200000000000 : ℝ) (88909433349/500000000000 : ℝ) (35563773341/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33691/262144 : ℝ)) (246015808771/250000000000 : ℝ) (196812647017/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33691/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246015808771/250000000000 : ℝ) (196812647017/200000000000 : ℝ) (496015808771/500000000000 : ℝ) (992031617543/1000000000000 : ℝ) (991999614457/1000000000000 : ℝ) (991999614459/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33691/262144 : ℝ)) 1 (496015808771/500000000000 : ℝ) (992031617543/1000000000000 : ℝ) (991999614457/1000000000000 : ℝ) (991999614459/1000000000000 : ℝ) (992015615999/1000000000000 : ℝ) (992015616001/1000000000000 : ℝ) (99201561587/100000000000 : ℝ) (7750121999/7812500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33691/262144 : ℝ)) 2 (992015615999/1000000000000 : ℝ) (992015616001/1000000000000 : ℝ) (99201561587/100000000000 : ℝ) (7750121999/7812500000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33691/262144 : ℝ)) 3 (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33691/262144 : ℝ)) 4 (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33691/262144 : ℝ)) 5 (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33691/262144 : ℝ)) 6 (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33691/262144 : ℝ)) 7 (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33691/262144 : ℝ))) (88909433349/500000000000 : ℝ) (35563773341/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33691/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88909433349/500000000000 : ℝ) (35563773341/200000000000 : ℝ) (588909433349/1000000000000 : ℝ) (588909433353/1000000000000 : ℝ) (210842872003/500000000000 : ℝ) (84337148803/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33691/262144 : ℝ))) 1 (588909433349/1000000000000 : ℝ) (588909433353/1000000000000 : ℝ) (210842872003/500000000000 : ℝ) (84337148803/200000000000 : ℝ) (505297588677/1000000000000 : ℝ) (126324397171/250000000000 : ℝ) (31145745631/62500000000 : ℝ) (62291491263/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33691/262144 : ℝ))) 2 (505297588677/1000000000000 : ℝ) (126324397171/250000000000 : ℝ) (31145745631/62500000000 : ℝ) (62291491263/125000000000 : ℝ) (250907379693/500000000000 : ℝ) (250907379697/500000000000 : ℝ) (31362667063/62500000000 : ℝ) (62725334127/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33691/262144 : ℝ))) 3 (250907379693/500000000000 : ℝ) (250907379697/500000000000 : ℝ) (31362667063/62500000000 : ℝ) (62725334127/125000000000 : ℝ) (501808716197/1000000000000 : ℝ) (100361743241/200000000000 : ℝ) (784076119/1562500000 : ℝ) (501808716169/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33691/262144 : ℝ))) 4 (501808716197/1000000000000 : ℝ) (100361743241/200000000000 : ℝ) (784076119/1562500000 : ℝ) (501808716169/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33691/262144 : ℝ))) 5 (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33691/262144 : ℝ))) 6 (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33691/262144 : ℝ))) 7 (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33691/262144 : ℝ)) hmem 8 (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33691/262144 : ℝ))) hcmem 8 (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33691/262144 : ℝ)) (496007807967/500000000000 : ℝ) (992015615937/1000000000000 : ℝ) (250904358089/500000000000 : ℝ) (501808716187/1000000000000 : ℝ) (397291774173/500000000000 : ℝ) (794583548363/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1258_exp_lower
  have heNumeric : (2054901600093/1000000000000 : ℝ)/4 ≤ Real.exp (-21314124719491/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901600093/1000000000000 : ℝ)/4 ≤ Real.exp ((16845/131072 : ℝ)-(794583548363/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16845/131072 : ℝ) (33691/262144 : ℝ) (794583548363/1000000000000 : ℝ) (2054901600093/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1259; no trusted numerical premise.
theorem cover8_leaf1259_exp_radius : (997993815392105907/1000000000000000000 : ℝ) ≤ Real.exp ((-8423/524288 : ℝ)/8) ∧ Real.exp ((-8423/524288 : ℝ)/8) ≤ (249498453848026477/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8423/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1259_exp_lower : (920113453497698707/1000000000000000000 : ℝ) ≤ Real.exp ((-8525649666353/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525649666353/12800000000000 : ℝ)/8) ≤ (230028363374424677/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525649666353/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1259_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725408911/250000000000 : ℝ) ≤ 4*Real.exp (33691/262144 : ℝ)*Real.exp (-mu (radius 8 (8423/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513725408911/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8423/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1259_exp_radius
  have hrNumeric : (984062765847/1000000000000 : ℝ) ≤ Real.exp (-8423/524288 : ℝ) ∧ Real.exp (-8423/524288 : ℝ) ≤ (123007845731/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984062765847/1000000000000 : ℝ) ≤ (radius 8 (8423/65536 : ℝ)) ∧ (radius 8 (8423/65536 : ℝ)) ≤ (123007845731/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8423/65536 : ℝ)) (984062765847/1000000000000 : ℝ) (123007845731/125000000000 : ℝ) (11113841467/62500000000 : ℝ) (177821463479/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8423/65536 : ℝ)) (984062765847/1000000000000 : ℝ) (123007845731/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8423/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984062765847/1000000000000 : ℝ) (123007845731/125000000000 : ℝ) (992031382923/1000000000000 : ℝ) (248007845731/250000000000 : ℝ) (495999688973/500000000000 : ℝ) (247999844487/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8423/65536 : ℝ)) 1 (992031382923/1000000000000 : ℝ) (248007845731/250000000000 : ℝ) (495999688973/500000000000 : ℝ) (247999844487/250000000000 : ℝ) (496007690217/500000000000 : ℝ) (248003845109/250000000000 : ℝ) (198403076061/200000000000 : ℝ) (992015380307/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8423/65536 : ℝ)) 2 (496007690217/500000000000 : ℝ) (248003845109/250000000000 : ℝ) (198403076061/200000000000 : ℝ) (992015380307/1000000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8423/65536 : ℝ)) 3 (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8423/65536 : ℝ)) 4 (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8423/65536 : ℝ)) 5 (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8423/65536 : ℝ)) 6 (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8423/65536 : ℝ)) 7 (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8423/65536 : ℝ))) (11113841467/62500000000 : ℝ) (177821463479/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8423/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11113841467/62500000000 : ℝ) (177821463479/1000000000000 : ℝ) (73613841467/125000000000 : ℝ) (29445536587/50000000000 : ℝ) (210844411517/500000000000 : ℝ) (421688823043/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8423/65536 : ℝ))) 1 (73613841467/125000000000 : ℝ) (29445536587/50000000000 : ℝ) (210844411517/500000000000 : ℝ) (421688823043/1000000000000 : ℝ) (101059955477/200000000000 : ℝ) (31581236087/62500000000 : ℝ) (498334298777/1000000000000 : ℝ) (99666859757/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8423/65536 : ℝ))) 2 (101059955477/200000000000 : ℝ) (31581236087/62500000000 : ℝ) (498334298777/1000000000000 : ℝ) (99666859757/200000000000 : ℝ) (501817038081/1000000000000 : ℝ) (501817038089/1000000000000 : ℝ) (250902476191/500000000000 : ℝ) (50180495239/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8423/65536 : ℝ))) 3 (501817038081/1000000000000 : ℝ) (501817038089/1000000000000 : ℝ) (250902476191/500000000000 : ℝ) (50180495239/100000000000 : ℝ) (501810995231/1000000000000 : ℝ) (12545274881/25000000000 : ℝ) (100362199039/200000000000 : ℝ) (125452748801/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8423/65536 : ℝ))) 4 (501810995231/1000000000000 : ℝ) (12545274881/25000000000 : ℝ) (100362199039/200000000000 : ℝ) (125452748801/250000000000 : ℝ) (501810995213/1000000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8423/65536 : ℝ))) 5 (501810995213/1000000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8423/65536 : ℝ))) 6 (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8423/65536 : ℝ))) 7 (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8423/65536 : ℝ)) hmem 8 (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8423/65536 : ℝ))) hcmem 8 (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8423/65536 : ℝ)) (992015380369/1000000000000 : ℝ) (248003845093/250000000000 : ℝ) (125452748803/250000000000 : ℝ) (250905497611/500000000000 : ℝ) (794587345741/1000000000000 : ℝ) (4966170911/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1259_exp_lower
  have heNumeric : (513725408911/250000000000 : ℝ)/4 ≤ Real.exp (-8525649666353/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725408911/250000000000 : ℝ)/4 ≤ Real.exp ((33691/262144 : ℝ)-(4966170911/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33691/262144 : ℝ) (8423/65536 : ℝ) (4966170911/6250000000 : ℝ) (513725408911/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1260; no trusted numerical premise.
theorem cover8_leaf1260_exp_radius : (498996877953520413/500000000000000000 : ℝ) ≤ Real.exp ((-33693/2097152 : ℝ)/8) ∧ Real.exp ((-33693/2097152 : ℝ)/8) ≤ (997993755907040827/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33693/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1260_exp_lower : (230028363873881399/250000000000000000 : ℝ) ≤ Real.exp ((-10657061805017/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657061805017/16000000000000 : ℝ)/8) ≤ (920113455495525597/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657061805017/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1260_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450835669/500000000000 : ℝ) ≤ 4*Real.exp (8423/65536 : ℝ)*Real.exp (-mu (radius 8 (33693/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450835669/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33693/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1260_exp_radius
  have hrNumeric : (984062296609/1000000000000 : ℝ) ≤ Real.exp (-33693/2097152 : ℝ) ∧ Real.exp (-33693/2097152 : ℝ) ≤ (98406229661/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984062296609/1000000000000 : ℝ) ≤ (radius 8 (33693/262144 : ℝ)) ∧ (radius 8 (33693/262144 : ℝ)) ≤ (98406229661/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33693/262144 : ℝ)) (984062296609/1000000000000 : ℝ) (98406229661/100000000000 : ℝ) (177824060213/1000000000000 : ℝ) (177824060219/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33693/262144 : ℝ)) (984062296609/1000000000000 : ℝ) (98406229661/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33693/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984062296609/1000000000000 : ℝ) (98406229661/100000000000 : ℝ) (62001946769/62500000000 : ℝ) (198406229661/200000000000 : ℝ) (198399828287/200000000000 : ℝ) (991999141437/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33693/262144 : ℝ)) 1 (62001946769/62500000000 : ℝ) (198406229661/200000000000 : ℝ) (198399828287/200000000000 : ℝ) (991999141437/1000000000000 : ℝ) (992015144869/1000000000000 : ℝ) (992015144871/1000000000000 : ℝ) (49600757237/50000000000 : ℝ) (496007572371/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33693/262144 : ℝ)) 2 (992015144869/1000000000000 : ℝ) (992015144871/1000000000000 : ℝ) (49600757237/50000000000 : ℝ) (496007572371/500000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33693/262144 : ℝ)) 3 (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33693/262144 : ℝ)) 4 (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33693/262144 : ℝ)) 5 (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33693/262144 : ℝ)) 6 (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33693/262144 : ℝ)) 7 (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33693/262144 : ℝ))) (177824060213/1000000000000 : ℝ) (177824060219/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33693/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177824060213/1000000000000 : ℝ) (177824060219/1000000000000 : ℝ) (294456015053/500000000000 : ℝ) (58891203011/100000000000 : ℝ) (210845951/500000000 : ℝ) (52711487751/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33693/262144 : ℝ))) 1 (294456015053/500000000000 : ℝ) (58891203011/100000000000 : ℝ) (210845951/500000000 : ℝ) (52711487751/125000000000 : ℝ) (505301966053/1000000000000 : ℝ) (505301966059/1000000000000 : ℝ) (49833666741/100000000000 : ℝ) (249168333709/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33693/262144 : ℝ))) 2 (505301966053/1000000000000 : ℝ) (505301966059/1000000000000 : ℝ) (49833666741/100000000000 : ℝ) (249168333709/500000000000 : ℝ) (501819316731/1000000000000 : ℝ) (501819316739/1000000000000 : ℝ) (15681475991/31250000000 : ℝ) (12545180793/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33693/262144 : ℝ))) 3 (501819316731/1000000000000 : ℝ) (501819316739/1000000000000 : ℝ) (15681475991/31250000000 : ℝ) (12545180793/25000000000 : ℝ) (501813274221/1000000000000 : ℝ) (50181327423/100000000000 : ℝ) (100362654837/200000000000 : ℝ) (250906637097/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33693/262144 : ℝ))) 4 (501813274221/1000000000000 : ℝ) (50181327423/100000000000 : ℝ) (100362654837/200000000000 : ℝ) (250906637097/500000000000 : ℝ) (501813274203/1000000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33693/262144 : ℝ))) 5 (501813274203/1000000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33693/262144 : ℝ))) 6 (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33693/262144 : ℝ))) 7 (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33693/262144 : ℝ)) hmem 8 (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33693/262144 : ℝ))) hcmem 8 (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33693/262144 : ℝ)) (248003786201/250000000000 : ℝ) (992015144807/1000000000000 : ℝ) (250906637101/500000000000 : ℝ) (125453318553/250000000000 : ℝ) (198647785767/250000000000 : ℝ) (794591143087/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1260_exp_lower
  have heNumeric : (1027450835669/500000000000 : ℝ)/4 ≤ Real.exp (-10657061805017/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450835669/500000000000 : ℝ)/4 ≤ Real.exp ((8423/65536 : ℝ)-(794591143087/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8423/65536 : ℝ) (33693/262144 : ℝ) (794591143087/1000000000000 : ℝ) (1027450835669/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1261; no trusted numerical premise.
theorem cover8_leaf1261_exp_radius : (997993696421979289/1000000000000000000 : ℝ) ≤ Real.exp ((-16847/1048576 : ℝ)/8) ∧ Real.exp ((-16847/1048576 : ℝ)/8) ≤ (99799369642197929/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16847/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1261_exp_lower : (230028364375695913/250000000000000000 : ℝ) ≤ Real.exp ((-42628246103123/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628246103123/64000000000000 : ℝ)/8) ≤ (920113457502783653/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628246103123/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1261_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901707201/1000000000000 : ℝ) ≤ 4*Real.exp (33693/262144 : ℝ)*Real.exp (-mu (radius 8 (16847/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901707201/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16847/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1261_exp_radius
  have hrNumeric : (246015456843/250000000000 : ℝ) ≤ Real.exp (-16847/1048576 : ℝ) ∧ Real.exp (-16847/1048576 : ℝ) ≤ (984061827373/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246015456843/250000000000 : ℝ) ≤ (radius 8 (16847/131072 : ℝ)) ∧ (radius 8 (16847/131072 : ℝ)) ≤ (984061827373/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16847/131072 : ℝ)) (246015456843/250000000000 : ℝ) (984061827373/1000000000000 : ℝ) (44456664227/250000000000 : ℝ) (35565331383/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16847/131072 : ℝ)) (246015456843/250000000000 : ℝ) (984061827373/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16847/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246015456843/250000000000 : ℝ) (984061827373/1000000000000 : ℝ) (496015456843/500000000000 : ℝ) (992030913687/1000000000000 : ℝ) (247999726231/250000000000 : ℝ) (495999452463/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16847/131072 : ℝ)) 1 (496015456843/500000000000 : ℝ) (992030913687/1000000000000 : ℝ) (247999726231/250000000000 : ℝ) (495999452463/500000000000 : ℝ) (198402981861/200000000000 : ℝ) (992014909307/1000000000000 : ℝ) (39680596367/40000000000 : ℝ) (496007454589/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16847/131072 : ℝ)) 2 (198402981861/200000000000 : ℝ) (992014909307/1000000000000 : ℝ) (39680596367/40000000000 : ℝ) (496007454589/500000000000 : ℝ) (24800372731/25000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16847/131072 : ℝ)) 3 (24800372731/25000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16847/131072 : ℝ)) 4 (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16847/131072 : ℝ)) 5 (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16847/131072 : ℝ)) 6 (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16847/131072 : ℝ)) 7 (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16847/131072 : ℝ))) (44456664227/250000000000 : ℝ) (35565331383/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16847/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44456664227/250000000000 : ℝ) (35565331383/200000000000 : ℝ) (294456664227/500000000000 : ℝ) (294456664229/500000000000 : ℝ) (42169498089/100000000000 : ℝ) (421694980899/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16847/131072 : ℝ))) 1 (294456664227/500000000000 : ℝ) (294456664229/500000000000 : ℝ) (42169498089/100000000000 : ℝ) (421694980899/1000000000000 : ℝ) (31581509667/62500000000 : ℝ) (505304154679/1000000000000 : ℝ) (249169517993/500000000000 : ℝ) (249169517997/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16847/131072 : ℝ))) 2 (31581509667/62500000000 : ℝ) (505304154679/1000000000000 : ℝ) (249169517993/500000000000 : ℝ) (249169517997/500000000000 : ℝ) (501821595329/1000000000000 : ℝ) (501821595337/1000000000000 : ℝ) (125452377747/250000000000 : ℝ) (501809510997/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16847/131072 : ℝ))) 3 (501821595329/1000000000000 : ℝ) (501821595337/1000000000000 : ℝ) (125452377747/250000000000 : ℝ) (501809510997/1000000000000 : ℝ) (250907776579/500000000000 : ℝ) (501815553167/1000000000000 : ℝ) (250907776561/500000000000 : ℝ) (501815553131/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16847/131072 : ℝ))) 4 (250907776579/500000000000 : ℝ) (501815553167/1000000000000 : ℝ) (250907776561/500000000000 : ℝ) (501815553131/1000000000000 : ℝ) (25090777657/50000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16847/131072 : ℝ))) 5 (25090777657/50000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16847/131072 : ℝ))) 6 (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16847/131072 : ℝ))) 7 (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16847/131072 : ℝ)) hmem 8 (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16847/131072 : ℝ))) hcmem 8 (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16847/131072 : ℝ)) (992014909239/1000000000000 : ℝ) (992014909243/1000000000000 : ℝ) (501815553139/1000000000000 : ℝ) (501815553149/1000000000000 : ℝ) (99324367539/125000000000 : ℝ) (198648735083/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1261_exp_lower
  have heNumeric : (2054901707201/1000000000000 : ℝ)/4 ≤ Real.exp (-42628246103123/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901707201/1000000000000 : ℝ)/4 ≤ Real.exp ((33693/262144 : ℝ)-(198648735083/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33693/262144 : ℝ) (16847/131072 : ℝ) (198648735083/250000000000 : ℝ) (2054901707201/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1262; no trusted numerical premise.
theorem cover8_leaf1262_exp_radius : (997993636936921299/1000000000000000000 : ℝ) ≤ Real.exp ((-33695/2097152 : ℝ)/8) ∧ Real.exp ((-33695/2097152 : ℝ)/8) ≤ (9979936369369213/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33695/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1262_exp_lower : (460056729759276381/500000000000000000 : ℝ) ≤ Real.exp ((-21314122490721/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314122490721/32000000000000 : ℝ)/8) ≤ (920113459518552763/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314122490721/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1262_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980348643/200000000000 : ℝ) ≤ 4*Real.exp (16847/131072 : ℝ)*Real.exp (-mu (radius 8 (33695/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (410980348643/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33695/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1262_exp_radius
  have hrNumeric : (196812271627/200000000000 : ℝ) ≤ Real.exp (-33695/2097152 : ℝ) ∧ Real.exp (-33695/2097152 : ℝ) ≤ (123007669767/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196812271627/200000000000 : ℝ) ≤ (radius 8 (33695/262144 : ℝ)) ∧ (radius 8 (33695/262144 : ℝ)) ≤ (123007669767/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33695/262144 : ℝ)) (196812271627/200000000000 : ℝ) (123007669767/125000000000 : ℝ) (35565850713/200000000000 : ℝ) (177829253571/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33695/262144 : ℝ)) (196812271627/200000000000 : ℝ) (123007669767/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33695/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196812271627/200000000000 : ℝ) (123007669767/125000000000 : ℝ) (992030679067/1000000000000 : ℝ) (248007669767/250000000000 : ℝ) (991998668413/1000000000000 : ℝ) (198399733683/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33695/262144 : ℝ)) 1 (992030679067/1000000000000 : ℝ) (248007669767/250000000000 : ℝ) (991998668413/1000000000000 : ℝ) (198399733683/200000000000 : ℝ) (49600733687/50000000000 : ℝ) (496007336871/500000000000 : ℝ) (99201467361/100000000000 : ℝ) (992014673613/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33695/262144 : ℝ)) 2 (49600733687/50000000000 : ℝ) (496007336871/500000000000 : ℝ) (99201467361/100000000000 : ℝ) (992014673613/1000000000000 : ℝ) (39680586947/40000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33695/262144 : ℝ)) 3 (39680586947/40000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33695/262144 : ℝ)) 4 (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33695/262144 : ℝ)) 5 (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33695/262144 : ℝ)) 6 (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33695/262144 : ℝ)) 7 (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33695/262144 : ℝ))) (35565850713/200000000000 : ℝ) (177829253571/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33695/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35565850713/200000000000 : ℝ) (177829253571/1000000000000 : ℝ) (294457313391/500000000000 : ℝ) (294457313393/500000000000 : ℝ) (6589032183/15625000000 : ℝ) (10542451493/25000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33695/262144 : ℝ))) 1 (294457313391/500000000000 : ℝ) (294457313393/500000000000 : ℝ) (6589032183/15625000000 : ℝ) (10542451493/25000000000 : ℝ) (505306343247/1000000000000 : ℝ) (505306343253/1000000000000 : ℝ) (49834140451/100000000000 : ℝ) (249170702259/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33695/262144 : ℝ))) 2 (505306343247/1000000000000 : ℝ) (505306343253/1000000000000 : ℝ) (49834140451/100000000000 : ℝ) (249170702259/500000000000 : ℝ) (250911936939/500000000000 : ℝ) (250911936943/500000000000 : ℝ) (501811790217/1000000000000 : ℝ) (20072471609/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33695/262144 : ℝ))) 3 (250911936939/500000000000 : ℝ) (250911936943/500000000000 : ℝ) (501811790217/1000000000000 : ℝ) (20072471609/40000000000 : ℝ) (501817832047/1000000000000 : ℝ) (62727229007/125000000000 : ℝ) (501817832011/1000000000000 : ℝ) (25090891601/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33695/262144 : ℝ))) 4 (501817832047/1000000000000 : ℝ) (62727229007/125000000000 : ℝ) (501817832011/1000000000000 : ℝ) (25090891601/50000000000 : ℝ) (501817832029/1000000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33695/262144 : ℝ))) 5 (501817832029/1000000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33695/262144 : ℝ))) 6 (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33695/262144 : ℝ))) 7 (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33695/262144 : ℝ)) hmem 8 (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33695/262144 : ℝ))) hcmem 8 (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33695/262144 : ℝ)) (496007336837/500000000000 : ℝ) (496007336839/500000000000 : ℝ) (125454458007/250000000000 : ℝ) (250908916019/500000000000 : ℝ) (794598737483/1000000000000 : ℝ) (794598737503/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1262_exp_lower
  have heNumeric : (410980348643/200000000000 : ℝ)/4 ≤ Real.exp (-21314122490721/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980348643/200000000000 : ℝ)/4 ≤ Real.exp ((16847/131072 : ℝ)-(794598737503/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16847/131072 : ℝ) (33695/262144 : ℝ) (794598737503/1000000000000 : ℝ) (410980348643/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1263; no trusted numerical premise.
theorem cover8_leaf1263_exp_radius : (498996788725933427/500000000000000000 : ℝ) ≤ Real.exp ((-1053/65536 : ℝ)/8) ∧ Real.exp ((-1053/65536 : ℝ)/8) ≤ (199598715490373371/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1053/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1263_exp_lower : (57507091346448623/62500000000000000 : ℝ) ≤ Real.exp ((-42628243854833/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628243854833/64000000000000 : ℝ)/8) ≤ (920113461543177969/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628243854833/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1263_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725444847/250000000000 : ℝ) ≤ 4*Real.exp (33695/262144 : ℝ)*Real.exp (-mu (radius 8 (1053/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (513725444847/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1053/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1263_exp_radius
  have hrNumeric : (492030444449/500000000000 : ℝ) ≤ Real.exp (-1053/65536 : ℝ) ∧ Real.exp (-1053/65536 : ℝ) ≤ (984060888899/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492030444449/500000000000 : ℝ) ≤ (radius 8 (1053/8192 : ℝ)) ∧ (radius 8 (1053/8192 : ℝ)) ≤ (984060888899/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1053/8192 : ℝ)) (492030444449/500000000000 : ℝ) (984060888899/1000000000000 : ℝ) (88915925091/500000000000 : ℝ) (44457962547/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1053/8192 : ℝ)) (492030444449/500000000000 : ℝ) (984060888899/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1053/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492030444449/500000000000 : ℝ) (984060888899/1000000000000 : ℝ) (992030444449/1000000000000 : ℝ) (19840608889/20000000000 : ℝ) (495999215951/500000000000 : ℝ) (30999950997/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1053/8192 : ℝ)) 1 (992030444449/1000000000000 : ℝ) (19840608889/20000000000 : ℝ) (495999215951/500000000000 : ℝ) (30999950997/31250000000 : ℝ) (39680577527/40000000000 : ℝ) (992014438177/1000000000000 : ℝ) (496007219023/500000000000 : ℝ) (31000451189/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1053/8192 : ℝ)) 2 (39680577527/40000000000 : ℝ) (992014438177/1000000000000 : ℝ) (496007219023/500000000000 : ℝ) (31000451189/31250000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1053/8192 : ℝ)) 3 (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1053/8192 : ℝ)) 4 (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1053/8192 : ℝ)) 5 (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1053/8192 : ℝ)) 6 (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1053/8192 : ℝ)) 7 (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1053/8192 : ℝ))) (88915925091/500000000000 : ℝ) (44457962547/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1053/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88915925091/500000000000 : ℝ) (44457962547/250000000000 : ℝ) (588915925091/1000000000000 : ℝ) (294457962547/500000000000 : ℝ) (13178160577/31250000000 : ℝ) (52712642309/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1053/8192 : ℝ))) 1 (588915925091/1000000000000 : ℝ) (294457962547/500000000000 : ℝ) (13178160577/31250000000 : ℝ) (52712642309/125000000000 : ℝ) (505308531777/1000000000000 : ℝ) (505308531783/1000000000000 : ℝ) (249171886491/500000000000 : ℝ) (498343772989/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1053/8192 : ℝ))) 2 (505308531777/1000000000000 : ℝ) (505308531783/1000000000000 : ℝ) (249171886491/500000000000 : ℝ) (498343772989/1000000000000 : ℝ) (501826152379/1000000000000 : ℝ) (250913076193/500000000000 : ℝ) (501814069397/1000000000000 : ℝ) (100362813881/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1053/8192 : ℝ))) 3 (501826152379/1000000000000 : ℝ) (250913076193/500000000000 : ℝ) (501814069397/1000000000000 : ℝ) (100362813881/200000000000 : ℝ) (62727513861/125000000000 : ℝ) (31363756931/62500000000 : ℝ) (501820110851/1000000000000 : ℝ) (25091005543/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1053/8192 : ℝ))) 4 (62727513861/125000000000 : ℝ) (31363756931/62500000000 : ℝ) (501820110851/1000000000000 : ℝ) (25091005543/50000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1053/8192 : ℝ))) 5 (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1053/8192 : ℝ))) 6 (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1053/8192 : ℝ))) 7 (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1053/8192 : ℝ)) hmem 8 (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1053/8192 : ℝ))) hcmem 8 (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1053/8192 : ℝ)) (99201443811/100000000000 : ℝ) (992014438113/1000000000000 : ℝ) (501820110869/1000000000000 : ℝ) (250910055439/500000000000 : ℝ) (39730126729/50000000000 : ℝ) (794602534597/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1263_exp_lower
  have heNumeric : (513725444847/250000000000 : ℝ)/4 ≤ Real.exp (-42628243854833/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725444847/250000000000 : ℝ)/4 ≤ Real.exp ((33695/262144 : ℝ)-(794602534597/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33695/262144 : ℝ) (1053/8192 : ℝ) (794602534597/1000000000000 : ℝ) (513725444847/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1264; no trusted numerical premise.
theorem cover8_leaf1264_exp_radius : (199598703593363191/200000000000000000 : ℝ) ≤ Real.exp ((-33697/2097152 : ℝ)/8) ∧ Real.exp ((-33697/2097152 : ℝ)/8) ≤ (249498379491703989/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33697/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1264_exp_lower : (460056731787984593/500000000000000000 : ℝ) ≤ Real.exp ((-266426517023/400000000000 : ℝ)/8) ∧ Real.exp ((-266426517023/400000000000 : ℝ)/8) ≤ (920113463575969187/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-266426517023/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1264_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901815707/1000000000000 : ℝ) ≤ 4*Real.exp (1053/8192 : ℝ)*Real.exp (-mu (radius 8 (33697/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901815707/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33697/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1264_exp_radius
  have hrNumeric : (984060419661/1000000000000 : ℝ) ≤ Real.exp (-33697/2097152 : ℝ) ∧ Real.exp (-33697/2097152 : ℝ) ≤ (492030209831/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984060419661/1000000000000 : ℝ) ≤ (radius 8 (33697/262144 : ℝ)) ∧ (radius 8 (33697/262144 : ℝ)) ≤ (492030209831/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33697/262144 : ℝ)) (984060419661/1000000000000 : ℝ) (492030209831/500000000000 : ℝ) (4445861169/25000000000 : ℝ) (177834446767/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33697/262144 : ℝ)) (984060419661/1000000000000 : ℝ) (492030209831/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33697/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984060419661/1000000000000 : ℝ) (492030209831/500000000000 : ℝ) (99203020983/100000000000 : ℝ) (992030209831/1000000000000 : ℝ) (15499971803/15625000000 : ℝ) (991998195393/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33697/262144 : ℝ)) 1 (99203020983/100000000000 : ℝ) (992030209831/1000000000000 : ℝ) (15499971803/15625000000 : ℝ) (991998195393/1000000000000 : ℝ) (992014202611/1000000000000 : ℝ) (248003550653/250000000000 : ℝ) (992014202481/1000000000000 : ℝ) (992014202483/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33697/262144 : ℝ)) 2 (992014202611/1000000000000 : ℝ) (248003550653/250000000000 : ℝ) (992014202481/1000000000000 : ℝ) (992014202483/1000000000000 : ℝ) (496007101273/500000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33697/262144 : ℝ)) 3 (496007101273/500000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33697/262144 : ℝ)) 4 (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33697/262144 : ℝ)) 5 (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33697/262144 : ℝ)) 6 (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33697/262144 : ℝ)) 7 (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33697/262144 : ℝ))) (4445861169/25000000000 : ℝ) (177834446767/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33697/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4445861169/25000000000 : ℝ) (177834446767/1000000000000 : ℝ) (29445861169/50000000000 : ℝ) (73614652923/125000000000 : ℝ) (421704217147/1000000000000 : ℝ) (105426054289/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33697/262144 : ℝ))) 1 (29445861169/50000000000 : ℝ) (73614652923/125000000000 : ℝ) (421704217147/1000000000000 : ℝ) (105426054289/250000000000 : ℝ) (505310720263/1000000000000 : ℝ) (50531072027/100000000000 : ℝ) (498346141401/1000000000000 : ℝ) (498346141409/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33697/262144 : ℝ))) 2 (505310720263/1000000000000 : ℝ) (50531072027/100000000000 : ℝ) (498346141401/1000000000000 : ℝ) (498346141409/1000000000000 : ℝ) (31364276927/62500000000 : ℝ) (12545710771/25000000000 : ℝ) (501816348529/1000000000000 : ℝ) (250908174269/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33697/262144 : ℝ))) 3 (31364276927/62500000000 : ℝ) (12545710771/25000000000 : ℝ) (501816348529/1000000000000 : ℝ) (250908174269/500000000000 : ℝ) (6272779871/12500000000 : ℝ) (501822389689/1000000000000 : ℝ) (125455597411/250000000000 : ℝ) (501822389653/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33697/262144 : ℝ))) 4 (6272779871/12500000000 : ℝ) (501822389689/1000000000000 : ℝ) (125455597411/250000000000 : ℝ) (501822389653/1000000000000 : ℝ) (250911194831/500000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33697/262144 : ℝ))) 5 (250911194831/500000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33697/262144 : ℝ))) 6 (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33697/262144 : ℝ))) 7 (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33697/262144 : ℝ)) hmem 8 (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33697/262144 : ℝ))) hcmem 8 (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33697/262144 : ℝ)) (198402840509/200000000000 : ℝ) (248003550637/250000000000 : ℝ) (501822389661/1000000000000 : ℝ) (501822389671/1000000000000 : ℝ) (794606331601/1000000000000 : ℝ) (39730316581/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1264_exp_lower
  have heNumeric : (2054901815707/1000000000000 : ℝ)/4 ≤ Real.exp (-266426517023/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901815707/1000000000000 : ℝ)/4 ≤ Real.exp ((1053/8192 : ℝ)-(39730316581/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1053/8192 : ℝ) (33697/262144 : ℝ) (39730316581/50000000000 : ℝ) (2054901815707/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1265; no trusted numerical premise.
theorem cover8_leaf1265_exp_radius : (997993458481768601/1000000000000000000 : ℝ) ≤ Real.exp ((-16849/1048576 : ℝ)/8) ∧ Real.exp ((-16849/1048576 : ℝ)/8) ≤ (498996729240884301/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16849/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1265_exp_lower : (460056732808750743/500000000000000000 : ℝ) ≤ Real.exp ((-42628241587663/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628241587663/64000000000000 : ℝ)/8) ≤ (920113465617501487/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628241587663/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1265_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450926091/500000000000 : ℝ) ≤ 4*Real.exp (33697/262144 : ℝ)*Real.exp (-mu (radius 8 (16849/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450926091/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16849/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1265_exp_radius
  have hrNumeric : (123007493803/125000000000 : ℝ) ≤ Real.exp (-16849/1048576 : ℝ) ∧ Real.exp (-16849/1048576 : ℝ) ≤ (39362398017/40000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123007493803/125000000000 : ℝ) ≤ (radius 8 (16849/131072 : ℝ)) ∧ (radius 8 (16849/131072 : ℝ)) ≤ (39362398017/40000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16849/131072 : ℝ)) (123007493803/125000000000 : ℝ) (39362398017/40000000000 : ℝ) (177837043299/1000000000000 : ℝ) (88918521653/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16849/131072 : ℝ)) (123007493803/125000000000 : ℝ) (39362398017/40000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16849/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123007493803/125000000000 : ℝ) (39362398017/40000000000 : ℝ) (248007493803/250000000000 : ℝ) (992029975213/1000000000000 : ℝ) (6199987243/6250000000 : ℝ) (495998979441/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16849/131072 : ℝ)) 1 (248007493803/250000000000 : ℝ) (992029975213/1000000000000 : ℝ) (6199987243/6250000000 : ℝ) (495998979441/500000000000 : ℝ) (496006983523/500000000000 : ℝ) (124001745881/125000000000 : ℝ) (248003491729/250000000000 : ℝ) (992013966919/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16849/131072 : ℝ)) 2 (496006983523/500000000000 : ℝ) (124001745881/125000000000 : ℝ) (248003491729/250000000000 : ℝ) (992013966919/1000000000000 : ℝ) (992013966981/1000000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16849/131072 : ℝ)) 3 (992013966981/1000000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16849/131072 : ℝ)) 4 (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16849/131072 : ℝ)) 5 (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16849/131072 : ℝ)) 6 (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16849/131072 : ℝ)) 7 (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16849/131072 : ℝ))) (177837043299/1000000000000 : ℝ) (88918521653/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16849/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177837043299/1000000000000 : ℝ) (88918521653/500000000000 : ℝ) (588918521649/1000000000000 : ℝ) (588918521653/1000000000000 : ℝ) (210853647881/500000000000 : ℝ) (421707295771/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16849/131072 : ℝ))) 1 (588918521649/1000000000000 : ℝ) (588918521653/1000000000000 : ℝ) (210853647881/500000000000 : ℝ) (421707295771/1000000000000 : ℝ) (101062581741/200000000000 : ℝ) (63164113589/125000000000 : ℝ) (62293563721/125000000000 : ℝ) (31146781861/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16849/131072 : ℝ))) 2 (101062581741/200000000000 : ℝ) (63164113589/125000000000 : ℝ) (62293563721/125000000000 : ℝ) (31146781861/62500000000 : ℝ) (125457677309/250000000000 : ℝ) (125457677311/250000000000 : ℝ) (501818627613/1000000000000 : ℝ) (501818627621/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16849/131072 : ℝ))) 3 (125457677309/250000000000 : ℝ) (125457677311/250000000000 : ℝ) (501818627613/1000000000000 : ℝ) (501818627621/1000000000000 : ℝ) (62728083553/125000000000 : ℝ) (501824668433/1000000000000 : ℝ) (125456167097/250000000000 : ℝ) (501824668397/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16849/131072 : ℝ))) 4 (62728083553/125000000000 : ℝ) (501824668433/1000000000000 : ℝ) (125456167097/250000000000 : ℝ) (501824668397/1000000000000 : ℝ) (250912334203/500000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16849/131072 : ℝ))) 5 (250912334203/500000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16849/131072 : ℝ))) 6 (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16849/131072 : ℝ))) 7 (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16849/131072 : ℝ)) hmem 8 (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16849/131072 : ℝ))) hcmem 8 (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16849/131072 : ℝ)) (49600698349/50000000000 : ℝ) (124001745873/125000000000 : ℝ) (100364933681/200000000000 : ℝ) (100364933683/200000000000 : ℝ) (794610128547/1000000000000 : ℝ) (794610128567/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1265_exp_lower
  have heNumeric : (1027450926091/500000000000 : ℝ)/4 ≤ Real.exp (-42628241587663/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450926091/500000000000 : ℝ)/4 ≤ Real.exp ((33697/262144 : ℝ)-(794610128567/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33697/262144 : ℝ) (16849/131072 : ℝ) (794610128567/1000000000000 : ℝ) (1027450926091/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1266; no trusted numerical premise.
theorem cover8_leaf1266_exp_radius : (997993398996724793/1000000000000000000 : ℝ) ≤ Real.exp ((-33699/2097152 : ℝ)/8) ∧ Real.exp ((-33699/2097152 : ℝ)/8) ≤ (498996699498362397/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33699/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1266_exp_lower : (460056733834347491/500000000000000000 : ℝ) ≤ Real.exp ((-4262824044627/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262824044627/6400000000000 : ℝ)/8) ≤ (920113467668694983/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262824044627/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1266_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490188883/100000000000 : ℝ) ≤ 4*Real.exp (16849/131072 : ℝ)*Real.exp (-mu (radius 8 (33699/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (205490188883/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33699/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1266_exp_radius
  have hrNumeric : (246014870297/250000000000 : ℝ) ≤ Real.exp (-33699/2097152 : ℝ) ∧ Real.exp (-33699/2097152 : ℝ) ≤ (984059481189/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246014870297/250000000000 : ℝ) ≤ (radius 8 (33699/262144 : ℝ)) ∧ (radius 8 (33699/262144 : ℝ)) ≤ (984059481189/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33699/262144 : ℝ)) (246014870297/250000000000 : ℝ) (984059481189/1000000000000 : ℝ) (177839639793/1000000000000 : ℝ) (889198199/5000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33699/262144 : ℝ)) (246014870297/250000000000 : ℝ) (984059481189/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33699/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246014870297/250000000000 : ℝ) (984059481189/1000000000000 : ℝ) (496014870297/500000000000 : ℝ) (198405948119/200000000000 : ℝ) (99199772237/100000000000 : ℝ) (991997722371/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33699/262144 : ℝ)) 1 (496014870297/500000000000 : ℝ) (198405948119/200000000000 : ℝ) (99199772237/100000000000 : ℝ) (991997722371/1000000000000 : ℝ) (496006865741/500000000000 : ℝ) (992013731483/1000000000000 : ℝ) (124001716419/125000000000 : ℝ) (496006865677/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33699/262144 : ℝ)) 2 (496006865741/500000000000 : ℝ) (992013731483/1000000000000 : ℝ) (124001716419/125000000000 : ℝ) (496006865677/500000000000 : ℝ) (992013731417/1000000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33699/262144 : ℝ)) 3 (992013731417/1000000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33699/262144 : ℝ)) 4 (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33699/262144 : ℝ)) 5 (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33699/262144 : ℝ)) 6 (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33699/262144 : ℝ)) 7 (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33699/262144 : ℝ))) (177839639793/1000000000000 : ℝ) (889198199/5000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33699/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177839639793/1000000000000 : ℝ) (889198199/5000000000 : ℝ) (73614977487/125000000000 : ℝ) (5889198199/10000000000 : ℝ) (4217103743/10000000000 : ℝ) (42171037431/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33699/262144 : ℝ))) 1 (73614977487/125000000000 : ℝ) (5889198199/10000000000 : ℝ) (4217103743/10000000000 : ℝ) (42171037431/100000000000 : ℝ) (252657548549/500000000000 : ℝ) (101063019421/200000000000 : ℝ) (498350878077/1000000000000 : ℝ) (249175439043/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33699/262144 : ℝ))) 2 (252657548549/500000000000 : ℝ) (101063019421/200000000000 : ℝ) (498350878077/1000000000000 : ℝ) (249175439043/500000000000 : ℝ) (501832987587/1000000000000 : ℝ) (125458246899/250000000000 : ℝ) (501820906643/1000000000000 : ℝ) (125455226663/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33699/262144 : ℝ))) 3 (501832987587/1000000000000 : ℝ) (125458246899/250000000000 : ℝ) (501820906643/1000000000000 : ℝ) (125455226663/250000000000 : ℝ) (100365389423/200000000000 : ℝ) (125456736781/250000000000 : ℝ) (250913473539/500000000000 : ℝ) (31364184193/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33699/262144 : ℝ))) 4 (100365389423/200000000000 : ℝ) (125456736781/250000000000 : ℝ) (250913473539/500000000000 : ℝ) (31364184193/62500000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33699/262144 : ℝ))) 5 (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33699/262144 : ℝ))) 6 (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33699/262144 : ℝ))) 7 (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33699/262144 : ℝ)) hmem 8 (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33699/262144 : ℝ))) hcmem 8 (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33699/262144 : ℝ)) (124001716427/125000000000 : ℝ) (992013731419/1000000000000 : ℝ) (62728368387/125000000000 : ℝ) (250913473553/500000000000 : ℝ) (794613925411/1000000000000 : ℝ) (79461392543/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1266_exp_lower
  have heNumeric : (205490188883/100000000000 : ℝ)/4 ≤ Real.exp (-4262824044627/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490188883/100000000000 : ℝ)/4 ≤ Real.exp ((16849/131072 : ℝ)-(79461392543/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16849/131072 : ℝ) (33699/262144 : ℝ) (79461392543/100000000000 : ℝ) (205490188883/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1267; no trusted numerical premise.
theorem cover8_leaf1267_exp_radius : (99799333951168453/100000000000000000 : ℝ) ≤ Real.exp ((-8425/524288 : ℝ)/8) ∧ Real.exp ((-8425/524288 : ℝ)/8) ≤ (997993339511684531/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8425/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1267_exp_lower : (460056734864142259/500000000000000000 : ℝ) ≤ Real.exp ((-8525647860041/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525647860041/12800000000000 : ℝ)/8) ≤ (920113469728284519/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525647860041/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1267_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725481407/250000000000 : ℝ) ≤ 4*Real.exp (33699/262144 : ℝ)*Real.exp (-mu (radius 8 (8425/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513725481407/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8425/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1267_exp_radius
  have hrNumeric : (61503688247/62500000000 : ℝ) ≤ Real.exp (-8425/524288 : ℝ) ∧ Real.exp (-8425/524288 : ℝ) ≤ (984059011953/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61503688247/62500000000 : ℝ) ≤ (radius 8 (8425/65536 : ℝ)) ∧ (radius 8 (8425/65536 : ℝ)) ≤ (984059011953/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8425/65536 : ℝ)) (61503688247/62500000000 : ℝ) (984059011953/1000000000000 : ℝ) (177842236249/1000000000000 : ℝ) (35568447251/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8425/65536 : ℝ)) (61503688247/62500000000 : ℝ) (984059011953/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8425/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61503688247/62500000000 : ℝ) (984059011953/1000000000000 : ℝ) (124003688247/125000000000 : ℝ) (992029505977/1000000000000 : ℝ) (991997485859/1000000000000 : ℝ) (991997485861/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8425/65536 : ℝ)) 1 (124003688247/125000000000 : ℝ) (992029505977/1000000000000 : ℝ) (991997485859/1000000000000 : ℝ) (991997485861/1000000000000 : ℝ) (992013495917/1000000000000 : ℝ) (992013495919/1000000000000 : ℝ) (248003373947/250000000000 : ℝ) (99201349579/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8425/65536 : ℝ)) 2 (992013495917/1000000000000 : ℝ) (992013495919/1000000000000 : ℝ) (248003373947/250000000000 : ℝ) (99201349579/100000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8425/65536 : ℝ)) 3 (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8425/65536 : ℝ)) 4 (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8425/65536 : ℝ)) 5 (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8425/65536 : ℝ)) 6 (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8425/65536 : ℝ)) 7 (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8425/65536 : ℝ))) (177842236249/1000000000000 : ℝ) (35568447251/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8425/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177842236249/1000000000000 : ℝ) (35568447251/200000000000 : ℝ) (147230279531/250000000000 : ℝ) (36807569883/62500000000 : ℝ) (105428363193/250000000000 : ℝ) (21085672639/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8425/65536 : ℝ))) 1 (147230279531/250000000000 : ℝ) (36807569883/62500000000 : ℝ) (105428363193/250000000000 : ℝ) (21085672639/50000000000 : ℝ) (63164660681/125000000000 : ℝ) (252658642727/500000000000 : ℝ) (3893384737/7812500000 : ℝ) (62294155793/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8425/65536 : ℝ))) 2 (63164660681/125000000000 : ℝ) (252658642727/500000000000 : ℝ) (3893384737/7812500000 : ℝ) (62294155793/125000000000 : ℝ) (125458816473/250000000000 : ℝ) (501835265899/1000000000000 : ℝ) (250911592813/500000000000 : ℝ) (250911592817/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8425/65536 : ℝ))) 3 (125458816473/250000000000 : ℝ) (501835265899/1000000000000 : ℝ) (250911592813/500000000000 : ℝ) (250911592817/500000000000 : ℝ) (501829225759/1000000000000 : ℝ) (501829225767/1000000000000 : ℝ) (250914612861/500000000000 : ℝ) (501829225731/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8425/65536 : ℝ))) 4 (501829225759/1000000000000 : ℝ) (501829225767/1000000000000 : ℝ) (250914612861/500000000000 : ℝ) (501829225731/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8425/65536 : ℝ))) 5 (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8425/65536 : ℝ))) 6 (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8425/65536 : ℝ))) 7 (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8425/65536 : ℝ)) hmem 8 (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8425/65536 : ℝ))) hcmem 8 (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8425/65536 : ℝ)) (248003373963/250000000000 : ℝ) (198402699171/200000000000 : ℝ) (25091461287/50000000000 : ℝ) (501829225749/1000000000000 : ℝ) (397308861101/500000000000 : ℝ) (39730886111/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1267_exp_lower
  have heNumeric : (513725481407/250000000000 : ℝ)/4 ≤ Real.exp (-8525647860041/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725481407/250000000000 : ℝ)/4 ≤ Real.exp ((33699/262144 : ℝ)-(39730886111/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33699/262144 : ℝ) (8425/65536 : ℝ) (39730886111/50000000000 : ℝ) (513725481407/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1268; no trusted numerical premise.
theorem cover8_leaf1268_exp_radius : (997993280026647813/1000000000000000000 : ℝ) ≤ Real.exp ((-33701/2097152 : ℝ)/8) ∧ Real.exp ((-33701/2097152 : ℝ)/8) ≤ (498996640013323907/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33701/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1268_exp_lower : (920113471796615137/1000000000000000000 : ℝ) ≤ Real.exp ((-10657059537319/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657059537319/16000000000000 : ℝ)/8) ≤ (460056735898307569/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657059537319/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1268_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450981291/500000000000 : ℝ) ≤ 4*Real.exp (8425/65536 : ℝ)*Real.exp (-mu (radius 8 (33701/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450981291/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33701/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1268_exp_radius
  have hrNumeric : (246014635679/250000000000 : ℝ) ≤ Real.exp (-33701/2097152 : ℝ) ∧ Real.exp (-33701/2097152 : ℝ) ≤ (984058542717/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246014635679/250000000000 : ℝ) ≤ (radius 8 (33701/262144 : ℝ)) ∧ (radius 8 (33701/262144 : ℝ)) ≤ (984058542717/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33701/262144 : ℝ)) (246014635679/250000000000 : ℝ) (984058542717/1000000000000 : ℝ) (35568966533/200000000000 : ℝ) (177844832671/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33701/262144 : ℝ)) (246014635679/250000000000 : ℝ) (984058542717/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33701/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246014635679/250000000000 : ℝ) (984058542717/1000000000000 : ℝ) (496014635679/500000000000 : ℝ) (992029271359/1000000000000 : ℝ) (991997249349/1000000000000 : ℝ) (19839944987/20000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33701/262144 : ℝ)) 1 (496014635679/500000000000 : ℝ) (992029271359/1000000000000 : ℝ) (991997249349/1000000000000 : ℝ) (19839944987/20000000000 : ℝ) (992013260353/1000000000000 : ℝ) (198402652071/200000000000 : ℝ) (15500207191/15625000000 : ℝ) (496006630113/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33701/262144 : ℝ)) 2 (992013260353/1000000000000 : ℝ) (198402652071/200000000000 : ℝ) (15500207191/15625000000 : ℝ) (496006630113/500000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33701/262144 : ℝ)) 3 (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33701/262144 : ℝ)) 4 (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33701/262144 : ℝ)) 5 (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33701/262144 : ℝ)) 6 (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33701/262144 : ℝ)) 7 (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33701/262144 : ℝ))) (35568966533/200000000000 : ℝ) (177844832671/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33701/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35568966533/200000000000 : ℝ) (177844832671/1000000000000 : ℝ) (147230604083/250000000000 : ℝ) (36807651021/62500000000 : ℝ) (421716531173/1000000000000 : ℝ) (421716531181/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33701/262144 : ℝ))) 1 (147230604083/250000000000 : ℝ) (36807651021/62500000000 : ℝ) (421716531173/1000000000000 : ℝ) (421716531181/1000000000000 : ℝ) (63164934219/125000000000 : ℝ) (505319473759/1000000000000 : ℝ) (249177807271/500000000000 : ℝ) (498355614549/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33701/262144 : ℝ))) 2 (63164934219/125000000000 : ℝ) (505319473759/1000000000000 : ℝ) (249177807271/500000000000 : ℝ) (498355614549/1000000000000 : ℝ) (501837544147/1000000000000 : ℝ) (250918772077/500000000000 : ℝ) (6272818307/12500000000 : ℝ) (62728183071/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33701/262144 : ℝ))) 3 (501837544147/1000000000000 : ℝ) (250918772077/500000000000 : ℝ) (6272818307/12500000000 : ℝ) (62728183071/125000000000 : ℝ) (501831504353/1000000000000 : ℝ) (501831504361/1000000000000 : ℝ) (501831504317/1000000000000 : ℝ) (20073260173/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33701/262144 : ℝ))) 4 (501831504353/1000000000000 : ℝ) (501831504361/1000000000000 : ℝ) (501831504317/1000000000000 : ℝ) (20073260173/40000000000 : ℝ) (100366300867/200000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33701/262144 : ℝ))) 5 (100366300867/200000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33701/262144 : ℝ))) 6 (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33701/262144 : ℝ))) 7 (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33701/262144 : ℝ)) hmem 8 (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33701/262144 : ℝ))) hcmem 8 (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33701/262144 : ℝ)) (1937525899/1953125000 : ℝ) (992013260291/1000000000000 : ℝ) (250915752167/500000000000 : ℝ) (501831504343/1000000000000 : ℝ) (198655379729/250000000000 : ℝ) (397310759467/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1268_exp_lower
  have heNumeric : (1027450981291/500000000000 : ℝ)/4 ≤ Real.exp (-10657059537319/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450981291/500000000000 : ℝ)/4 ≤ Real.exp ((8425/65536 : ℝ)-(397310759467/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8425/65536 : ℝ) (33701/262144 : ℝ) (397310759467/500000000000 : ℝ) (1027450981291/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1269; no trusted numerical premise.
theorem cover8_leaf1269_exp_radius : (498996610270807321/500000000000000000 : ℝ) ≤ Real.exp ((-16851/1048576 : ℝ)/8) ∧ Real.exp ((-16851/1048576 : ℝ)/8) ≤ (997993220541614643/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16851/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1269_exp_lower : (920113473874031881/1000000000000000000 : ℝ) ≤ Real.exp ((-42628236993291/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628236993291/64000000000000 : ℝ)/8) ≤ (460056736937015941/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628236993291/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1269_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450999849/500000000000 : ℝ) ≤ 4*Real.exp (33701/262144 : ℝ)*Real.exp (-mu (radius 8 (16851/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450999849/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16851/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1269_exp_radius
  have hrNumeric : (984058073481/1000000000000 : ℝ) ≤ Real.exp (-16851/1048576 : ℝ) ∧ Real.exp (-16851/1048576 : ℝ) ≤ (492029036741/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984058073481/1000000000000 : ℝ) ≤ (radius 8 (16851/131072 : ℝ)) ∧ (radius 8 (16851/131072 : ℝ)) ≤ (492029036741/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16851/131072 : ℝ)) (984058073481/1000000000000 : ℝ) (492029036741/500000000000 : ℝ) (44461857259/250000000000 : ℝ) (177847429043/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16851/131072 : ℝ)) (984058073481/1000000000000 : ℝ) (492029036741/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16851/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984058073481/1000000000000 : ℝ) (492029036741/500000000000 : ℝ) (49601451837/50000000000 : ℝ) (992029036741/1000000000000 : ℝ) (495998506419/500000000000 : ℝ) (24799925321/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16851/131072 : ℝ)) 1 (49601451837/50000000000 : ℝ) (992029036741/1000000000000 : ℝ) (495998506419/500000000000 : ℝ) (24799925321/25000000000 : ℝ) (992013024789/1000000000000 : ℝ) (992013024791/1000000000000 : ℝ) (992013024659/1000000000000 : ℝ) (496006512331/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16851/131072 : ℝ)) 2 (992013024789/1000000000000 : ℝ) (992013024791/1000000000000 : ℝ) (992013024659/1000000000000 : ℝ) (496006512331/500000000000 : ℝ) (248003256181/250000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16851/131072 : ℝ)) 3 (248003256181/250000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16851/131072 : ℝ)) 4 (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16851/131072 : ℝ)) 5 (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16851/131072 : ℝ)) 6 (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16851/131072 : ℝ)) 7 (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16851/131072 : ℝ))) (44461857259/250000000000 : ℝ) (177847429043/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16851/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44461857259/250000000000 : ℝ) (177847429043/1000000000000 : ℝ) (294461857259/500000000000 : ℝ) (294461857261/500000000000 : ℝ) (421719609499/1000000000000 : ℝ) (105429902377/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16851/131072 : ℝ))) 1 (294461857259/500000000000 : ℝ) (294461857261/500000000000 : ℝ) (421719609499/1000000000000 : ℝ) (105429902377/250000000000 : ℝ) (63165207751/125000000000 : ℝ) (101064332403/200000000000 : ℝ) (49835798269/100000000000 : ℝ) (249178991349/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16851/131072 : ℝ))) 2 (63165207751/125000000000 : ℝ) (101064332403/200000000000 : ℝ) (49835798269/100000000000 : ℝ) (249178991349/500000000000 : ℝ) (501839822349/1000000000000 : ℝ) (501839822357/1000000000000 : ℝ) (501827743441/1000000000000 : ℝ) (10036554869/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16851/131072 : ℝ))) 3 (501839822349/1000000000000 : ℝ) (501839822357/1000000000000 : ℝ) (501827743441/1000000000000 : ℝ) (10036554869/20000000000 : ℝ) (100366756579/200000000000 : ℝ) (62729222863/125000000000 : ℝ) (250916891429/500000000000 : ℝ) (125458445717/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16851/131072 : ℝ))) 4 (100366756579/200000000000 : ℝ) (62729222863/125000000000 : ℝ) (250916891429/500000000000 : ℝ) (125458445717/250000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16851/131072 : ℝ))) 5 (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16851/131072 : ℝ))) 6 (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16851/131072 : ℝ))) 7 (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16851/131072 : ℝ)) hmem 8 (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16851/131072 : ℝ))) hcmem 8 (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16851/131072 : ℝ)) (992013024723/1000000000000 : ℝ) (992013024727/1000000000000 : ℝ) (125458445719/250000000000 : ℝ) (250916891443/500000000000 : ℝ) (794625315549/1000000000000 : ℝ) (794625315569/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1269_exp_lower
  have heNumeric : (1027450999849/500000000000 : ℝ)/4 ≤ Real.exp (-42628236993291/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450999849/500000000000 : ℝ)/4 ≤ Real.exp ((33701/262144 : ℝ)-(794625315569/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33701/262144 : ℝ) (16851/131072 : ℝ) (794625315569/1000000000000 : ℝ) (1027450999849/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1270; no trusted numerical premise.
theorem cover8_leaf1270_exp_radius : (124749145132073127/125000000000000000 : ℝ) ≤ Real.exp ((-33703/2097152 : ℝ)/8) ∧ Real.exp ((-33703/2097152 : ℝ)/8) ≤ (997993161056585017/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33703/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1270_exp_lower : (115014184495052467/125000000000000000 : ℝ) ≤ Real.exp ((-21314117916157/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314117916157/32000000000000 : ℝ)/8) ≤ (920113475960419737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314117916157/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1270_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451018487/500000000000 : ℝ) ≤ 4*Real.exp (16851/131072 : ℝ)*Real.exp (-mu (radius 8 (33703/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451018487/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33703/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1270_exp_radius
  have hrNumeric : (492028802123/500000000000 : ℝ) ≤ Real.exp (-33703/2097152 : ℝ) ∧ Real.exp (-33703/2097152 : ℝ) ≤ (984057604247/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492028802123/500000000000 : ℝ) ≤ (radius 8 (33703/262144 : ℝ)) ∧ (radius 8 (33703/262144 : ℝ)) ≤ (984057604247/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33703/262144 : ℝ)) (492028802123/500000000000 : ℝ) (984057604247/1000000000000 : ℝ) (22231253171/125000000000 : ℝ) (1422800203/8000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33703/262144 : ℝ)) (492028802123/500000000000 : ℝ) (984057604247/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33703/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492028802123/500000000000 : ℝ) (984057604247/1000000000000 : ℝ) (992028802123/1000000000000 : ℝ) (248007200531/250000000000 : ℝ) (123999597041/125000000000 : ℝ) (991996776329/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33703/262144 : ℝ)) 1 (992028802123/1000000000000 : ℝ) (248007200531/250000000000 : ℝ) (123999597041/125000000000 : ℝ) (991996776329/1000000000000 : ℝ) (39680511569/40000000000 : ℝ) (992012789227/1000000000000 : ℝ) (124001598637/125000000000 : ℝ) (496006394549/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33703/262144 : ℝ)) 2 (39680511569/40000000000 : ℝ) (992012789227/1000000000000 : ℝ) (124001598637/125000000000 : ℝ) (496006394549/500000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33703/262144 : ℝ)) 3 (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33703/262144 : ℝ)) 4 (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33703/262144 : ℝ)) 5 (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33703/262144 : ℝ)) 6 (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33703/262144 : ℝ)) 7 (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33703/262144 : ℝ))) (22231253171/125000000000 : ℝ) (1422800203/8000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33703/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22231253171/125000000000 : ℝ) (1422800203/8000000000 : ℝ) (147231253171/250000000000 : ℝ) (36807813293/62500000000 : ℝ) (84344537551/200000000000 : ℝ) (84344537553/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33703/262144 : ℝ))) 1 (147231253171/250000000000 : ℝ) (36807813293/62500000000 : ℝ) (84344537551/200000000000 : ℝ) (84344537553/200000000000 : ℝ) (505323850219/1000000000000 : ℝ) (505323850227/1000000000000 : ℝ) (99672070157/200000000000 : ℝ) (249180175397/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33703/262144 : ℝ))) 2 (505323850219/1000000000000 : ℝ) (505323850227/1000000000000 : ℝ) (99672070157/200000000000 : ℝ) (249180175397/500000000000 : ℝ) (250921050251/500000000000 : ℝ) (501842100511/1000000000000 : ℝ) (501830022273/1000000000000 : ℝ) (501830022283/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33703/262144 : ℝ))) 3 (250921050251/500000000000 : ℝ) (501842100511/1000000000000 : ℝ) (501830022273/1000000000000 : ℝ) (501830022283/1000000000000 : ℝ) (501836061387/1000000000000 : ℝ) (501836061397/1000000000000 : ℝ) (501836061351/1000000000000 : ℝ) (501836061361/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33703/262144 : ℝ))) 4 (501836061387/1000000000000 : ℝ) (501836061397/1000000000000 : ℝ) (501836061351/1000000000000 : ℝ) (501836061361/1000000000000 : ℝ) (501836061369/1000000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33703/262144 : ℝ))) 5 (501836061369/1000000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33703/262144 : ℝ))) 6 (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33703/262144 : ℝ))) 7 (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33703/262144 : ℝ)) hmem 8 (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33703/262144 : ℝ))) hcmem 8 (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33703/262144 : ℝ)) (24800319729/25000000000 : ℝ) (992012789163/1000000000000 : ℝ) (62729507671/125000000000 : ℝ) (501836061379/1000000000000 : ℝ) (158925822421/200000000000 : ℝ) (397314556063/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1270_exp_lower
  have heNumeric : (1027451018487/500000000000 : ℝ)/4 ≤ Real.exp (-21314117916157/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451018487/500000000000 : ℝ)/4 ≤ Real.exp ((16851/131072 : ℝ)-(397314556063/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16851/131072 : ℝ) (33703/262144 : ℝ) (397314556063/500000000000 : ℝ) (1027451018487/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1271; no trusted numerical premise.
theorem cover8_leaf1271_exp_radius : (124749137696444867/125000000000000000 : ℝ) ≤ Real.exp ((-4213/262144 : ℝ)/8) ∧ Real.exp ((-4213/262144 : ℝ)/8) ≤ (997993101571558937/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4213/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1271_exp_lower : (460056739027256773/500000000000000000 : ℝ) ≤ Real.exp ((-42628234667049/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628234667049/64000000000000 : ℝ)/8) ≤ (920113478054513547/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628234667049/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1271_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725518597/250000000000 : ℝ) ≤ 4*Real.exp (33703/262144 : ℝ)*Real.exp (-mu (radius 8 (4213/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (513725518597/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4213/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1271_exp_radius
  have hrNumeric : (98405713501/100000000000 : ℝ) ≤ Real.exp (-4213/262144 : ℝ) ∧ Real.exp (-4213/262144 : ℝ) ≤ (984057135011/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98405713501/100000000000 : ℝ) ≤ (radius 8 (4213/32768 : ℝ)) ∧ (radius 8 (4213/32768 : ℝ)) ≤ (984057135011/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4213/32768 : ℝ)) (98405713501/100000000000 : ℝ) (984057135011/1000000000000 : ℝ) (177852621667/1000000000000 : ℝ) (177852621673/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4213/32768 : ℝ)) (98405713501/100000000000 : ℝ) (984057135011/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4213/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98405713501/100000000000 : ℝ) (984057135011/1000000000000 : ℝ) (198405713501/200000000000 : ℝ) (496014283753/500000000000 : ℝ) (991996539817/1000000000000 : ℝ) (991996539819/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4213/32768 : ℝ)) 1 (198405713501/200000000000 : ℝ) (496014283753/500000000000 : ℝ) (991996539817/1000000000000 : ℝ) (991996539819/1000000000000 : ℝ) (992012553661/1000000000000 : ℝ) (992012553663/1000000000000 : ℝ) (992012553531/1000000000000 : ℝ) (496006276767/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4213/32768 : ℝ)) 2 (992012553661/1000000000000 : ℝ) (992012553663/1000000000000 : ℝ) (992012553531/1000000000000 : ℝ) (496006276767/500000000000 : ℝ) (248003138399/250000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4213/32768 : ℝ)) 3 (248003138399/250000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4213/32768 : ℝ)) 4 (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4213/32768 : ℝ)) 5 (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4213/32768 : ℝ)) 6 (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4213/32768 : ℝ)) 7 (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4213/32768 : ℝ))) (177852621667/1000000000000 : ℝ) (177852621673/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4213/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177852621667/1000000000000 : ℝ) (177852621673/1000000000000 : ℝ) (588926310833/1000000000000 : ℝ) (588926310837/1000000000000 : ℝ) (421725765951/1000000000000 : ℝ) (421725765959/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4213/32768 : ℝ))) 1 (588926310833/1000000000000 : ℝ) (588926310837/1000000000000 : ℝ) (421725765951/1000000000000 : ℝ) (421725765959/1000000000000 : ℝ) (63165754799/125000000000 : ℝ) (252663019199/500000000000 : ℝ) (99672543767/200000000000 : ℝ) (249181359421/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4213/32768 : ℝ))) 2 (63165754799/125000000000 : ℝ) (252663019199/500000000000 : ℝ) (99672543767/200000000000 : ℝ) (249181359421/500000000000 : ℝ) (501844378613/1000000000000 : ℝ) (25092218931/50000000000 : ℝ) (501832301063/1000000000000 : ℝ) (501832301071/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4213/32768 : ℝ))) 3 (501844378613/1000000000000 : ℝ) (25092218931/50000000000 : ℝ) (501832301063/1000000000000 : ℝ) (501832301071/1000000000000 : ℝ) (250919169919/500000000000 : ℝ) (250919169923/500000000000 : ℝ) (501838339801/1000000000000 : ℝ) (50183833981/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4213/32768 : ℝ))) 4 (250919169919/500000000000 : ℝ) (250919169923/500000000000 : ℝ) (501838339801/1000000000000 : ℝ) (50183833981/100000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4213/32768 : ℝ))) 5 (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4213/32768 : ℝ))) 6 (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4213/32768 : ℝ))) 7 (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4213/32768 : ℝ)) hmem 8 (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4213/32768 : ℝ))) hcmem 8 (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4213/32768 : ℝ)) (198402510719/200000000000 : ℝ) (992012553599/1000000000000 : ℝ) (501838339819/1000000000000 : ℝ) (125459584957/250000000000 : ℝ) (397316454299/500000000000 : ℝ) (99329113577/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1271_exp_lower
  have heNumeric : (513725518597/250000000000 : ℝ)/4 ≤ Real.exp (-42628234667049/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725518597/250000000000 : ℝ)/4 ≤ Real.exp ((33703/262144 : ℝ)-(99329113577/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33703/262144 : ℝ) (4213/32768 : ℝ) (99329113577/125000000000 : ℝ) (513725518597/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1272; no trusted numerical premise.
theorem cover8_leaf1272_exp_radius : (997993042086536401/1000000000000000000 : ℝ) ≤ Real.exp ((-33705/2097152 : ℝ)/8) ∧ Real.exp ((-33705/2097152 : ℝ)/8) ≤ (498996521043268201/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33705/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1272_exp_lower : (230028370039509631/250000000000000000 : ℝ) ≤ Real.exp ((-5328529187067/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328529187067/8000000000000 : ℝ)/8) ≤ (36804539206321541/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328529187067/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1272_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902111971/1000000000000 : ℝ) ≤ 4*Real.exp (4213/32768 : ℝ)*Real.exp (-mu (radius 8 (33705/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902111971/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33705/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1272_exp_radius
  have hrNumeric : (39362266631/40000000000 : ℝ) ≤ Real.exp (-33705/2097152 : ℝ) ∧ Real.exp (-33705/2097152 : ℝ) ≤ (61503541611/62500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39362266631/40000000000 : ℝ) ≤ (radius 8 (33705/262144 : ℝ)) ∧ (radius 8 (33705/262144 : ℝ)) ≤ (61503541611/62500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33705/262144 : ℝ)) (39362266631/40000000000 : ℝ) (61503541611/62500000000 : ℝ) (177855217921/1000000000000 : ℝ) (177855217927/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33705/262144 : ℝ)) (39362266631/40000000000 : ℝ) (61503541611/62500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33705/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39362266631/40000000000 : ℝ) (61503541611/62500000000 : ℝ) (992028332887/1000000000000 : ℝ) (124003541611/125000000000 : ℝ) (991996303307/1000000000000 : ℝ) (247999075827/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33705/262144 : ℝ)) 1 (992028332887/1000000000000 : ℝ) (124003541611/125000000000 : ℝ) (991996303307/1000000000000 : ℝ) (247999075827/250000000000 : ℝ) (992012318097/1000000000000 : ℝ) (496006159049/500000000000 : ℝ) (992012317967/1000000000000 : ℝ) (992012317969/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33705/262144 : ℝ)) 2 (992012318097/1000000000000 : ℝ) (496006159049/500000000000 : ℝ) (992012317967/1000000000000 : ℝ) (992012317969/1000000000000 : ℝ) (62000769877/62500000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33705/262144 : ℝ)) 3 (62000769877/62500000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33705/262144 : ℝ)) 4 (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33705/262144 : ℝ)) 5 (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33705/262144 : ℝ)) 6 (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33705/262144 : ℝ)) 7 (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33705/262144 : ℝ))) (177855217921/1000000000000 : ℝ) (177855217927/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33705/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177855217921/1000000000000 : ℝ) (177855217927/1000000000000 : ℝ) (920199389/1562500000 : ℝ) (147231902241/250000000000 : ℝ) (42172884407/100000000000 : ℝ) (210864422039/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33705/262144 : ℝ))) 1 (920199389/1562500000 : ℝ) (147231902241/250000000000 : ℝ) (42172884407/100000000000 : ℝ) (210864422039/500000000000 : ℝ) (101065645303/200000000000 : ℝ) (505328226521/1000000000000 : ℝ) (249182543413/500000000000 : ℝ) (498365086833/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33705/262144 : ℝ))) 2 (101065645303/200000000000 : ℝ) (505328226521/1000000000000 : ℝ) (249182543413/500000000000 : ℝ) (498365086833/1000000000000 : ℝ) (50184665667/100000000000 : ℝ) (501846656677/1000000000000 : ℝ) (501834579799/1000000000000 : ℝ) (501834579807/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33705/262144 : ℝ))) 3 (50184665667/100000000000 : ℝ) (501846656677/1000000000000 : ℝ) (501834579799/1000000000000 : ℝ) (501834579807/1000000000000 : ℝ) (250920309117/500000000000 : ℝ) (250920309121/500000000000 : ℝ) (250920309099/500000000000 : ℝ) (250920309103/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33705/262144 : ℝ))) 4 (250920309117/500000000000 : ℝ) (250920309121/500000000000 : ℝ) (250920309099/500000000000 : ℝ) (250920309103/500000000000 : ℝ) (62730077277/125000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33705/262144 : ℝ))) 5 (62730077277/125000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33705/262144 : ℝ))) 6 (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33705/262144 : ℝ))) 7 (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33705/262144 : ℝ)) hmem 8 (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33705/262144 : ℝ))) hcmem 8 (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33705/262144 : ℝ)) (992012318031/1000000000000 : ℝ) (496006159017/500000000000 : ℝ) (100368123643/200000000000 : ℝ) (31365038639/62500000000 : ℝ) (397318352503/500000000000 : ℝ) (3104049629/3906250000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1272_exp_lower
  have heNumeric : (2054902111971/1000000000000 : ℝ)/4 ≤ Real.exp (-5328529187067/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902111971/1000000000000 : ℝ)/4 ≤ Real.exp ((4213/32768 : ℝ)-(3104049629/3906250000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4213/32768 : ℝ) (33705/262144 : ℝ) (3104049629/3906250000 : ℝ) (2054902111971/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1273; no trusted numerical premise.
theorem cover8_leaf1273_exp_radius : (249498245650379353/250000000000000000 : ℝ) ≤ Real.exp ((-16853/1048576 : ℝ)/8) ∧ Real.exp ((-16853/1048576 : ℝ)/8) ≤ (997992982601517413/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16853/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1273_exp_lower : (460056741135382321/500000000000000000 : ℝ) ≤ Real.exp ((-42628232320903/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628232320903/64000000000000 : ℝ)/8) ≤ (920113482270764643/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628232320903/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1273_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027451074859/500000000000 : ℝ) ≤ 4*Real.exp (33705/262144 : ℝ)*Real.exp (-mu (radius 8 (16853/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027451074859/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16853/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1273_exp_radius
  have hrNumeric : (984056196541/1000000000000 : ℝ) ≤ Real.exp (-16853/1048576 : ℝ) ∧ Real.exp (-16853/1048576 : ℝ) ≤ (492028098271/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984056196541/1000000000000 : ℝ) ≤ (radius 8 (16853/131072 : ℝ)) ∧ (radius 8 (16853/131072 : ℝ)) ≤ (492028098271/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16853/131072 : ℝ)) (984056196541/1000000000000 : ℝ) (492028098271/500000000000 : ℝ) (17785781413/100000000000 : ℝ) (177857814137/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16853/131072 : ℝ)) (984056196541/1000000000000 : ℝ) (492028098271/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16853/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984056196541/1000000000000 : ℝ) (492028098271/500000000000 : ℝ) (99202809827/100000000000 : ℝ) (992028098271/1000000000000 : ℝ) (991996066797/1000000000000 : ℝ) (495998033399/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16853/131072 : ℝ)) 1 (99202809827/100000000000 : ℝ) (992028098271/1000000000000 : ℝ) (991996066797/1000000000000 : ℝ) (495998033399/500000000000 : ℝ) (992012082533/1000000000000 : ℝ) (198402416507/200000000000 : ℝ) (248003020601/250000000000 : ℝ) (496006041203/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16853/131072 : ℝ)) 2 (992012082533/1000000000000 : ℝ) (198402416507/200000000000 : ℝ) (248003020601/250000000000 : ℝ) (496006041203/500000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16853/131072 : ℝ)) 3 (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16853/131072 : ℝ)) 4 (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16853/131072 : ℝ)) 5 (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16853/131072 : ℝ)) 6 (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16853/131072 : ℝ)) 7 (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16853/131072 : ℝ))) (17785781413/100000000000 : ℝ) (177857814137/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16853/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17785781413/100000000000 : ℝ) (177857814137/1000000000000 : ℝ) (117785781413/200000000000 : ℝ) (588928907069/1000000000000 : ℝ) (210865961057/500000000000 : ℝ) (421731922123/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16853/131072 : ℝ))) 1 (117785781413/200000000000 : ℝ) (588928907069/1000000000000 : ℝ) (210865961057/500000000000 : ℝ) (421731922123/1000000000000 : ℝ) (505330414589/1000000000000 : ℝ) (126332603649/250000000000 : ℝ) (498367454761/1000000000000 : ℝ) (498367454769/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16853/131072 : ℝ))) 2 (505330414589/1000000000000 : ℝ) (126332603649/250000000000 : ℝ) (498367454761/1000000000000 : ℝ) (498367454769/1000000000000 : ℝ) (20073957387/40000000000 : ℝ) (501848934683/1000000000000 : ℝ) (250918429241/500000000000 : ℝ) (501836858491/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16853/131072 : ℝ))) 3 (20073957387/40000000000 : ℝ) (501848934683/1000000000000 : ℝ) (250918429241/500000000000 : ℝ) (501836858491/1000000000000 : ℝ) (250921448289/500000000000 : ℝ) (501842896587/1000000000000 : ℝ) (250921448271/500000000000 : ℝ) (501842896551/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16853/131072 : ℝ))) 4 (250921448289/500000000000 : ℝ) (501842896587/1000000000000 : ℝ) (250921448271/500000000000 : ℝ) (501842896551/1000000000000 : ℝ) (6273036207/12500000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16853/131072 : ℝ))) 5 (6273036207/12500000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16853/131072 : ℝ))) 6 (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16853/131072 : ℝ))) 7 (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16853/131072 : ℝ)) hmem 8 (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16853/131072 : ℝ))) hcmem 8 (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16853/131072 : ℝ)) (248003020617/250000000000 : ℝ) (992012082471/1000000000000 : ℝ) (501842896559/1000000000000 : ℝ) (501842896569/1000000000000 : ℝ) (198660125333/250000000000 : ℝ) (99330062669/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1273_exp_lower
  have heNumeric : (1027451074859/500000000000 : ℝ)/4 ≤ Real.exp (-42628232320903/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027451074859/500000000000 : ℝ)/4 ≤ Real.exp ((33705/262144 : ℝ)-(99330062669/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33705/262144 : ℝ) (16853/131072 : ℝ) (99330062669/125000000000 : ℝ) (1027451074859/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1274; no trusted numerical premise.
theorem cover8_leaf1274_exp_radius : (62374557694781373/62500000000000000 : ℝ) ≤ Real.exp ((-33707/2097152 : ℝ)/8) ∧ Real.exp ((-33707/2097152 : ℝ)/8) ≤ (997992923116501969/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33707/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1274_exp_lower : (920113484391426743/1000000000000000000 : ℝ) ≤ Real.exp ((-21314115570427/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314115570427/32000000000000 : ℝ)/8) ≤ (115014185548928343/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314115570427/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1274_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054902187607/1000000000000 : ℝ) ≤ 4*Real.exp (16853/131072 : ℝ)*Real.exp (-mu (radius 8 (33707/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054902187607/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33707/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1274_exp_radius
  have hrNumeric : (492027863653/500000000000 : ℝ) ≤ Real.exp (-33707/2097152 : ℝ) ∧ Real.exp (-33707/2097152 : ℝ) ≤ (984055727307/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492027863653/500000000000 : ℝ) ≤ (radius 8 (33707/262144 : ℝ)) ∧ (radius 8 (33707/262144 : ℝ)) ≤ (984055727307/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33707/262144 : ℝ)) (492027863653/500000000000 : ℝ) (984055727307/1000000000000 : ℝ) (88930205153/500000000000 : ℝ) (22232551289/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33707/262144 : ℝ)) (492027863653/500000000000 : ℝ) (984055727307/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33707/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492027863653/500000000000 : ℝ) (984055727307/1000000000000 : ℝ) (992027863653/1000000000000 : ℝ) (496013931827/500000000000 : ℝ) (495997915143/500000000000 : ℝ) (61999739393/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33707/262144 : ℝ)) 1 (992027863653/1000000000000 : ℝ) (496013931827/500000000000 : ℝ) (495997915143/500000000000 : ℝ) (61999739393/62500000000 : ℝ) (992011846969/1000000000000 : ℝ) (992011846971/1000000000000 : ℝ) (24800296171/25000000000 : ℝ) (496005923421/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33707/262144 : ℝ)) 2 (992011846969/1000000000000 : ℝ) (992011846971/1000000000000 : ℝ) (24800296171/25000000000 : ℝ) (496005923421/500000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33707/262144 : ℝ)) 3 (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33707/262144 : ℝ)) 4 (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33707/262144 : ℝ)) 5 (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33707/262144 : ℝ)) 6 (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33707/262144 : ℝ)) 7 (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33707/262144 : ℝ))) (88930205153/500000000000 : ℝ) (22232551289/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33707/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88930205153/500000000000 : ℝ) (22232551289/125000000000 : ℝ) (588930205153/1000000000000 : ℝ) (147232551289/250000000000 : ℝ) (13179218753/31250000000 : ℝ) (52716875013/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33707/262144 : ℝ))) 1 (588930205153/1000000000000 : ℝ) (147232551289/250000000000 : ℝ) (13179218753/31250000000 : ℝ) (52716875013/125000000000 : ℝ) (1973955479/3906250000 : ℝ) (50533260263/100000000000 : ℝ) (62296227831/125000000000 : ℝ) (99673964531/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33707/262144 : ℝ))) 2 (1973955479/3906250000 : ℝ) (50533260263/100000000000 : ℝ) (62296227831/125000000000 : ℝ) (99673964531/200000000000 : ℝ) (125462803159/250000000000 : ℝ) (501851212643/1000000000000 : ℝ) (250919568561/500000000000 : ℝ) (50183913713/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33707/262144 : ℝ))) 3 (125462803159/250000000000 : ℝ) (501851212643/1000000000000 : ℝ) (250919568561/500000000000 : ℝ) (50183913713/100000000000 : ℝ) (501845174879/1000000000000 : ℝ) (501845174887/1000000000000 : ℝ) (250922587421/500000000000 : ℝ) (501845174851/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33707/262144 : ℝ))) 4 (501845174879/1000000000000 : ℝ) (501845174887/1000000000000 : ℝ) (250922587421/500000000000 : ℝ) (501845174851/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33707/262144 : ℝ))) 5 (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33707/262144 : ℝ))) 6 (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33707/262144 : ℝ))) 7 (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33707/262144 : ℝ)) hmem 8 (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33707/262144 : ℝ))) hcmem 8 (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33707/262144 : ℝ)) (124001480863/125000000000 : ℝ) (992011846907/1000000000000 : ℝ) (25092258743/50000000000 : ℝ) (501845174869/1000000000000 : ℝ) (794644297593/1000000000000 : ℝ) (794644297611/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1274_exp_lower
  have heNumeric : (2054902187607/1000000000000 : ℝ)/4 ≤ Real.exp (-21314115570427/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054902187607/1000000000000 : ℝ)/4 ≤ Real.exp ((16853/131072 : ℝ)-(794644297611/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16853/131072 : ℝ) (33707/262144 : ℝ) (794644297611/1000000000000 : ℝ) (2054902187607/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1250_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1250_certificate
#check SmaleRate.Proofs.cover8_leaf1251_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1251_certificate
#check SmaleRate.Proofs.cover8_leaf1252_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1252_certificate
#check SmaleRate.Proofs.cover8_leaf1253_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1253_certificate
#check SmaleRate.Proofs.cover8_leaf1254_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1254_certificate
#check SmaleRate.Proofs.cover8_leaf1255_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1255_certificate
#check SmaleRate.Proofs.cover8_leaf1256_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1256_certificate
#check SmaleRate.Proofs.cover8_leaf1257_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1257_certificate
#check SmaleRate.Proofs.cover8_leaf1258_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1258_certificate
#check SmaleRate.Proofs.cover8_leaf1259_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1259_certificate
#check SmaleRate.Proofs.cover8_leaf1260_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1260_certificate
#check SmaleRate.Proofs.cover8_leaf1261_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1261_certificate
#check SmaleRate.Proofs.cover8_leaf1262_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1262_certificate
#check SmaleRate.Proofs.cover8_leaf1263_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1263_certificate
#check SmaleRate.Proofs.cover8_leaf1264_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1264_certificate
#check SmaleRate.Proofs.cover8_leaf1265_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1265_certificate
#check SmaleRate.Proofs.cover8_leaf1266_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1266_certificate
#check SmaleRate.Proofs.cover8_leaf1267_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1267_certificate
#check SmaleRate.Proofs.cover8_leaf1268_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1268_certificate
#check SmaleRate.Proofs.cover8_leaf1269_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1269_certificate
#check SmaleRate.Proofs.cover8_leaf1270_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1270_certificate
#check SmaleRate.Proofs.cover8_leaf1271_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1271_certificate
#check SmaleRate.Proofs.cover8_leaf1272_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1272_certificate
#check SmaleRate.Proofs.cover8_leaf1273_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1273_certificate
#check SmaleRate.Proofs.cover8_leaf1274_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1274_certificate
