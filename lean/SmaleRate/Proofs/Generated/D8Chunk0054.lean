/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1350; no trusted numerical premise.
theorem cover8_leaf1350_exp_radius : (997988402265702623/1000000000000000000 : ℝ) ≤ Real.exp ((-33783/2097152 : ℝ)/8) ∧ Real.exp ((-33783/2097152 : ℝ)/8) ≤ (31187137570803207/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33783/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1350_exp_lower : (57507104453697191/62500000000000000 : ℝ) ≤ Real.exp ((-21314063578869/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314063578869/32000000000000 : ℝ)/8) ≤ (920113671259155057/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314063578869/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1350_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513726381571/250000000000 : ℝ) ≤ 4*Real.exp (16891/131072 : ℝ)*Real.exp (-mu (radius 8 (33783/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513726381571/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33783/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1350_exp_radius
  have hrNumeric : (984020066143/1000000000000 : ℝ) ≤ Real.exp (-33783/2097152 : ℝ) ∧ Real.exp (-33783/2097152 : ℝ) ≤ (30750627067/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984020066143/1000000000000 : ℝ) ≤ (radius 8 (33783/262144 : ℝ)) ∧ (radius 8 (33783/262144 : ℝ)) ≤ (30750627067/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33783/262144 : ℝ)) (984020066143/1000000000000 : ℝ) (30750627067/31250000000 : ℝ) (178057601427/1000000000000 : ℝ) (178057601433/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33783/262144 : ℝ)) (984020066143/1000000000000 : ℝ) (30750627067/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33783/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984020066143/1000000000000 : ℝ) (30750627067/31250000000 : ℝ) (992010033071/1000000000000 : ℝ) (62000627067/62500000000 : ℝ) (991977855671/1000000000000 : ℝ) (991977855673/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33783/262144 : ℝ)) 1 (992010033071/1000000000000 : ℝ) (62000627067/62500000000 : ℝ) (991977855671/1000000000000 : ℝ) (991977855673/1000000000000 : ℝ) (991993944371/1000000000000 : ℝ) (991993944373/1000000000000 : ℝ) (12399924303/12500000000 : ℝ) (991993944243/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33783/262144 : ℝ)) 2 (991993944371/1000000000000 : ℝ) (991993944373/1000000000000 : ℝ) (12399924303/12500000000 : ℝ) (991993944243/1000000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33783/262144 : ℝ)) 3 (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33783/262144 : ℝ)) 4 (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33783/262144 : ℝ)) 5 (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33783/262144 : ℝ)) 6 (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33783/262144 : ℝ)) 7 (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33783/262144 : ℝ))) (178057601427/1000000000000 : ℝ) (178057601433/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33783/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178057601427/1000000000000 : ℝ) (178057601433/1000000000000 : ℝ) (589028800713/1000000000000 : ℝ) (589028800717/1000000000000 : ℝ) (42196872091/100000000000 : ℝ) (210984360459/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33783/262144 : ℝ))) 1 (589028800713/1000000000000 : ℝ) (589028800717/1000000000000 : ℝ) (42196872091/100000000000 : ℝ) (210984360459/500000000000 : ℝ) (505498760811/1000000000000 : ℝ) (252749380409/500000000000 : ℝ) (498549626031/1000000000000 : ℝ) (249274813019/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33783/262144 : ℝ))) 2 (505498760811/1000000000000 : ℝ) (252749380409/500000000000 : ℝ) (498549626031/1000000000000 : ℝ) (249274813019/500000000000 : ℝ) (502024193421/1000000000000 : ℝ) (125506048357/250000000000 : ℝ) (62751521167/125000000000 : ℝ) (3921970073/7812500000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33783/262144 : ℝ))) 3 (502024193421/1000000000000 : ℝ) (125506048357/250000000000 : ℝ) (62751521167/125000000000 : ℝ) (3921970073/7812500000 : ℝ) (251009090689/500000000000 : ℝ) (251009090693/500000000000 : ℝ) (251009090671/500000000000 : ℝ) (502018181351/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33783/262144 : ℝ))) 4 (251009090689/500000000000 : ℝ) (251009090693/500000000000 : ℝ) (251009090671/500000000000 : ℝ) (502018181351/1000000000000 : ℝ) (6275227267/12500000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33783/262144 : ℝ))) 5 (6275227267/12500000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33783/262144 : ℝ))) 6 (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33783/262144 : ℝ))) 7 (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33783/262144 : ℝ)) hmem 8 (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33783/262144 : ℝ))) hcmem 8 (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33783/262144 : ℝ)) (198398788861/200000000000 : ℝ) (247998486077/250000000000 : ℝ) (502018181359/1000000000000 : ℝ) (502018181369/1000000000000 : ℝ) (99366573731/125000000000 : ℝ) (794932589867/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1350_exp_lower
  have heNumeric : (513726381571/250000000000 : ℝ)/4 ≤ Real.exp (-21314063578869/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513726381571/250000000000 : ℝ)/4 ≤ Real.exp ((16891/131072 : ℝ)-(794932589867/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16891/131072 : ℝ) (33783/262144 : ℝ) (794932589867/1000000000000 : ℝ) (513726381571/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1351; no trusted numerical premise.
theorem cover8_leaf1351_exp_radius : (997988342780960189/1000000000000000000 : ℝ) ≤ Real.exp ((-4223/262144 : ℝ)/8) ∧ Real.exp ((-4223/262144 : ℝ)/8) ≤ (99798834278096019/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4223/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1351_exp_lower : (920113674055181029/1000000000000000000 : ℝ) ≤ Real.exp ((-42628125601881/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628125601881/64000000000000 : ℝ)/8) ≤ (92011367405518103/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628125601881/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1351_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905576239/1000000000000 : ℝ) ≤ 4*Real.exp (33783/262144 : ℝ)*Real.exp (-mu (radius 8 (4223/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905576239/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4223/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1351_exp_radius
  have hrNumeric : (492009798463/500000000000 : ℝ) ≤ Real.exp (-4223/262144 : ℝ) ∧ Real.exp (-4223/262144 : ℝ) ≤ (984019596927/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492009798463/500000000000 : ℝ) ≤ (radius 8 (4223/32768 : ℝ)) ∧ (radius 8 (4223/32768 : ℝ)) ≤ (984019596927/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4223/32768 : ℝ)) (492009798463/500000000000 : ℝ) (984019596927/1000000000000 : ℝ) (35612038899/200000000000 : ℝ) (178060194501/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4223/32768 : ℝ)) (492009798463/500000000000 : ℝ) (984019596927/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4223/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492009798463/500000000000 : ℝ) (984019596927/1000000000000 : ℝ) (992009798463/1000000000000 : ℝ) (15500153101/15625000000 : ℝ) (198395523833/200000000000 : ℝ) (991977619167/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4223/32768 : ℝ)) 1 (992009798463/1000000000000 : ℝ) (15500153101/15625000000 : ℝ) (198395523833/200000000000 : ℝ) (991977619167/1000000000000 : ℝ) (495996854407/500000000000 : ℝ) (61999606801/62500000000 : ℝ) (991993708683/1000000000000 : ℝ) (495996854343/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4223/32768 : ℝ)) 2 (495996854407/500000000000 : ℝ) (61999606801/62500000000 : ℝ) (991993708683/1000000000000 : ℝ) (495996854343/500000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4223/32768 : ℝ)) 3 (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4223/32768 : ℝ)) 4 (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4223/32768 : ℝ)) 5 (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4223/32768 : ℝ)) 6 (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4223/32768 : ℝ)) 7 (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4223/32768 : ℝ))) (35612038899/200000000000 : ℝ) (178060194501/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4223/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35612038899/200000000000 : ℝ) (178060194501/1000000000000 : ℝ) (589030097247/1000000000000 : ℝ) (589030097251/1000000000000 : ℝ) (210985896741/500000000000 : ℝ) (42197179349/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4223/32768 : ℝ))) 1 (589030097247/1000000000000 : ℝ) (589030097251/1000000000000 : ℝ) (210985896741/500000000000 : ℝ) (42197179349/100000000000 : ℝ) (126375236341/250000000000 : ℝ) (505500945371/1000000000000 : ℝ) (62318998727/125000000000 : ℝ) (7789874841/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4223/32768 : ℝ))) 2 (126375236341/250000000000 : ℝ) (505500945371/1000000000000 : ℝ) (62318998727/125000000000 : ℝ) (7789874841/15625000000 : ℝ) (50202646759/100000000000 : ℝ) (251013233799/500000000000 : ℝ) (502014444179/1000000000000 : ℝ) (125503611047/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4223/32768 : ℝ))) 3 (50202646759/100000000000 : ℝ) (251013233799/500000000000 : ℝ) (502014444179/1000000000000 : ℝ) (125503611047/250000000000 : ℝ) (125505113971/250000000000 : ℝ) (502020455893/1000000000000 : ℝ) (62752556981/125000000000 : ℝ) (251010227929/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4223/32768 : ℝ))) 4 (125505113971/250000000000 : ℝ) (502020455893/1000000000000 : ℝ) (62752556981/125000000000 : ℝ) (251010227929/500000000000 : ℝ) (251010227933/500000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4223/32768 : ℝ))) 5 (251010227933/500000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4223/32768 : ℝ))) 6 (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4223/32768 : ℝ))) 7 (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4223/32768 : ℝ)) hmem 8 (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4223/32768 : ℝ))) hcmem 8 (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4223/32768 : ℝ)) (247998427187/250000000000 : ℝ) (991993708751/1000000000000 : ℝ) (100404091173/200000000000 : ℝ) (125505113969/250000000000 : ℝ) (794936380233/1000000000000 : ℝ) (397468190127/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1351_exp_lower
  have heNumeric : (2054905576239/1000000000000 : ℝ)/4 ≤ Real.exp (-42628125601881/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905576239/1000000000000 : ℝ)/4 ≤ Real.exp ((33783/262144 : ℝ)-(397468190127/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33783/262144 : ℝ) (4223/32768 : ℝ) (397468190127/500000000000 : ℝ) (2054905576239/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1352; no trusted numerical premise.
theorem cover8_leaf1352_exp_radius : (9979882832962213/10000000000000000 : ℝ) ≤ Real.exp ((-33785/2097152 : ℝ)/8) ∧ Real.exp ((-33785/2097152 : ℝ)/8) ≤ (997988283296221301/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33785/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1352_exp_lower : (184022735372012621/200000000000000000 : ℝ) ≤ Real.exp ((-5328515505137/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328515505137/8000000000000 : ℝ)/8) ≤ (460056838430031553/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328515505137/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1352_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431601647/62500000000 : ℝ) ≤ 4*Real.exp (4223/32768 : ℝ)*Real.exp (-mu (radius 8 (33785/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (128431601647/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33785/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1352_exp_radius
  have hrNumeric : (984019127709/1000000000000 : ℝ) ≤ Real.exp (-33785/2097152 : ℝ) ∧ Real.exp (-33785/2097152 : ℝ) ≤ (98401912771/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984019127709/1000000000000 : ℝ) ≤ (radius 8 (33785/262144 : ℝ)) ∧ (radius 8 (33785/262144 : ℝ)) ≤ (98401912771/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33785/262144 : ℝ)) (984019127709/1000000000000 : ℝ) (98401912771/100000000000 : ℝ) (44515696881/250000000000 : ℝ) (17806278753/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33785/262144 : ℝ)) (984019127709/1000000000000 : ℝ) (98401912771/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33785/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984019127709/1000000000000 : ℝ) (98401912771/100000000000 : ℝ) (496004781927/500000000000 : ℝ) (198401912771/200000000000 : ℝ) (49598869133/50000000000 : ℝ) (991977382661/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33785/262144 : ℝ)) 1 (496004781927/500000000000 : ℝ) (198401912771/200000000000 : ℝ) (49598869133/50000000000 : ℝ) (991977382661/1000000000000 : ℝ) (991993473257/1000000000000 : ℝ) (495996736629/500000000000 : ℝ) (495996736563/500000000000 : ℝ) (123999184141/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33785/262144 : ℝ)) 2 (991993473257/1000000000000 : ℝ) (495996736629/500000000000 : ℝ) (495996736563/500000000000 : ℝ) (123999184141/125000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33785/262144 : ℝ)) 3 (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33785/262144 : ℝ)) 4 (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33785/262144 : ℝ)) 5 (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33785/262144 : ℝ)) 6 (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33785/262144 : ℝ)) 7 (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33785/262144 : ℝ))) (44515696881/250000000000 : ℝ) (17806278753/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33785/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44515696881/250000000000 : ℝ) (17806278753/100000000000 : ℝ) (294515696881/500000000000 : ℝ) (117806278753/200000000000 : ℝ) (210987432993/500000000000 : ℝ) (210987432997/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33785/262144 : ℝ))) 1 (294515696881/500000000000 : ℝ) (117806278753/200000000000 : ℝ) (210987432993/500000000000 : ℝ) (210987432997/500000000000 : ℝ) (252751564937/500000000000 : ℝ) (12637578247/25000000000 : ℝ) (9971087071/20000000000 : ℝ) (498554353557/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33785/262144 : ℝ))) 2 (252751564937/500000000000 : ℝ) (12637578247/25000000000 : ℝ) (9971087071/20000000000 : ℝ) (498554353557/1000000000000 : ℝ) (31376796357/62500000000 : ℝ) (502028741719/1000000000000 : ℝ) (3922005617/7812500000 : ℝ) (502016718983/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33785/262144 : ℝ))) 3 (31376796357/62500000000 : ℝ) (502028741719/1000000000000 : ℝ) (3922005617/7812500000 : ℝ) (502016718983/1000000000000 : ℝ) (62752841293/125000000000 : ℝ) (502022730351/1000000000000 : ℝ) (125505682577/250000000000 : ℝ) (125505682579/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33785/262144 : ℝ))) 4 (62752841293/125000000000 : ℝ) (502022730351/1000000000000 : ℝ) (125505682577/250000000000 : ℝ) (125505682579/250000000000 : ℝ) (251011365163/500000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33785/262144 : ℝ))) 5 (251011365163/500000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33785/262144 : ℝ))) 6 (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33785/262144 : ℝ))) 7 (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33785/262144 : ℝ)) hmem 8 (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33785/262144 : ℝ))) hcmem 8 (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33785/262144 : ℝ)) (991993473191/1000000000000 : ℝ) (991993473193/1000000000000 : ℝ) (20080909213/40000000000 : ℝ) (251011365167/500000000000 : ℝ) (794940170547/1000000000000 : ℝ) (198735042641/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1352_exp_lower
  have heNumeric : (128431601647/62500000000 : ℝ)/4 ≤ Real.exp (-5328515505137/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431601647/62500000000 : ℝ)/4 ≤ Real.exp ((4223/32768 : ℝ)-(198735042641/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4223/32768 : ℝ) (33785/262144 : ℝ) (198735042641/250000000000 : ℝ) (128431601647/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1353; no trusted numerical premise.
theorem cover8_leaf1353_exp_radius : (997988223811485957/1000000000000000000 : ℝ) ≤ Real.exp ((-16893/1048576 : ℝ)/8) ∧ Real.exp ((-16893/1048576 : ℝ)/8) ≤ (498994111905742979/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16893/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1353_exp_lower : (920113679673226213/1000000000000000000 : ℝ) ≤ Real.exp ((-42628122475703/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628122475703/64000000000000 : ℝ)/8) ≤ (460056839836613107/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628122475703/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1353_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452838307/500000000000 : ℝ) ≤ 4*Real.exp (33785/262144 : ℝ)*Real.exp (-mu (radius 8 (16893/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452838307/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16893/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1353_exp_radius
  have hrNumeric : (246004664623/250000000000 : ℝ) ≤ Real.exp (-16893/1048576 : ℝ) ∧ Real.exp (-16893/1048576 : ℝ) ≤ (984018658493/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246004664623/250000000000 : ℝ) ≤ (radius 8 (16893/131072 : ℝ)) ∧ (radius 8 (16893/131072 : ℝ)) ≤ (984018658493/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16893/131072 : ℝ)) (246004664623/250000000000 : ℝ) (984018658493/1000000000000 : ℝ) (89032690257/500000000000 : ℝ) (4451634513/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16893/131072 : ℝ)) (246004664623/250000000000 : ℝ) (984018658493/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16893/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246004664623/250000000000 : ℝ) (984018658493/1000000000000 : ℝ) (496004664623/500000000000 : ℝ) (992009329247/1000000000000 : ℝ) (495988573077/500000000000 : ℝ) (198395429231/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16893/131072 : ℝ)) 1 (496004664623/500000000000 : ℝ) (992009329247/1000000000000 : ℝ) (495988573077/500000000000 : ℝ) (198395429231/200000000000 : ℝ) (9919932377/10000000000 : ℝ) (991993237701/1000000000000 : ℝ) (991993237569/1000000000000 : ℝ) (991993237571/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16893/131072 : ℝ)) 2 (9919932377/10000000000 : ℝ) (991993237701/1000000000000 : ℝ) (991993237569/1000000000000 : ℝ) (991993237571/1000000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16893/131072 : ℝ)) 3 (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16893/131072 : ℝ)) 4 (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16893/131072 : ℝ)) 5 (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16893/131072 : ℝ)) 6 (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16893/131072 : ℝ)) 7 (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16893/131072 : ℝ))) (89032690257/500000000000 : ℝ) (4451634513/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16893/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89032690257/500000000000 : ℝ) (4451634513/25000000000 : ℝ) (589032690257/1000000000000 : ℝ) (29451634513/50000000000 : ℝ) (21098896921/50000000000 : ℝ) (421977938429/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16893/131072 : ℝ))) 1 (589032690257/1000000000000 : ℝ) (29451634513/50000000000 : ℝ) (21098896921/50000000000 : ℝ) (421977938429/1000000000000 : ℝ) (252752657169/500000000000 : ℝ) (101101062869/200000000000 : ℝ) (498556717231/1000000000000 : ℝ) (498556717239/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16893/131072 : ℝ))) 2 (252752657169/500000000000 : ℝ) (101101062869/200000000000 : ℝ) (498556717231/1000000000000 : ℝ) (498556717239/1000000000000 : ℝ) (62753876973/125000000000 : ℝ) (31376938487/62500000000 : ℝ) (502018993723/1000000000000 : ℝ) (125504748433/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16893/131072 : ℝ))) 3 (62753876973/125000000000 : ℝ) (31376938487/62500000000 : ℝ) (502018993723/1000000000000 : ℝ) (125504748433/250000000000 : ℝ) (502025004753/1000000000000 : ℝ) (251012502381/500000000000 : ℝ) (502025004717/1000000000000 : ℝ) (502025004727/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16893/131072 : ℝ))) 4 (502025004753/1000000000000 : ℝ) (251012502381/500000000000 : ℝ) (502025004717/1000000000000 : ℝ) (502025004727/1000000000000 : ℝ) (100405000947/200000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16893/131072 : ℝ))) 5 (100405000947/200000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16893/131072 : ℝ))) 6 (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16893/131072 : ℝ))) 7 (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16893/131072 : ℝ)) hmem 8 (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16893/131072 : ℝ))) hcmem 8 (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16893/131072 : ℝ)) (495996618817/500000000000 : ℝ) (247998309409/250000000000 : ℝ) (251012502367/500000000000 : ℝ) (100405000949/200000000000 : ℝ) (397471980391/500000000000 : ℝ) (397471980401/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1353_exp_lower
  have heNumeric : (1027452838307/500000000000 : ℝ)/4 ≤ Real.exp (-42628122475703/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452838307/500000000000 : ℝ)/4 ≤ Real.exp ((33785/262144 : ℝ)-(397471980401/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33785/262144 : ℝ) (16893/131072 : ℝ) (397471980401/500000000000 : ℝ) (1027452838307/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1354; no trusted numerical premise.
theorem cover8_leaf1354_exp_radius : (997988164326754159/1000000000000000000 : ℝ) ≤ Real.exp ((-33787/2097152 : ℝ)/8) ∧ Real.exp ((-33787/2097152 : ℝ)/8) ≤ (12474852054084427/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33787/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1354_exp_lower : (92011368249513041/100000000000000000 : ℝ) ≤ Real.exp ((-21314060452723/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314060452723/32000000000000 : ℝ)/8) ≤ (920113682495130411/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314060452723/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1354_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905727031/1000000000000 : ℝ) ≤ 4*Real.exp (16893/131072 : ℝ)*Real.exp (-mu (radius 8 (33787/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905727031/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33787/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1354_exp_radius
  have hrNumeric : (39360727571/40000000000 : ℝ) ≤ Real.exp (-33787/2097152 : ℝ) ∧ Real.exp (-33787/2097152 : ℝ) ≤ (246004547319/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (39360727571/40000000000 : ℝ) ≤ (radius 8 (33787/262144 : ℝ)) ∧ (radius 8 (33787/262144 : ℝ)) ≤ (246004547319/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33787/262144 : ℝ)) (39360727571/40000000000 : ℝ) (246004547319/250000000000 : ℝ) (35613594693/200000000000 : ℝ) (178067973471/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33787/262144 : ℝ)) (39360727571/40000000000 : ℝ) (246004547319/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33787/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (39360727571/40000000000 : ℝ) (246004547319/250000000000 : ℝ) (992009094637/1000000000000 : ℝ) (496004547319/500000000000 : ℝ) (61998556853/62500000000 : ℝ) (991976909649/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33787/262144 : ℝ)) 1 (992009094637/1000000000000 : ℝ) (496004547319/500000000000 : ℝ) (61998556853/62500000000 : ℝ) (991976909649/1000000000000 : ℝ) (495996501071/500000000000 : ℝ) (30999781317/31250000000 : ℝ) (991993002011/1000000000000 : ℝ) (991993002013/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33787/262144 : ℝ)) 2 (495996501071/500000000000 : ℝ) (30999781317/31250000000 : ℝ) (991993002011/1000000000000 : ℝ) (991993002013/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33787/262144 : ℝ)) 3 (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33787/262144 : ℝ)) 4 (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33787/262144 : ℝ)) 5 (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33787/262144 : ℝ)) 6 (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33787/262144 : ℝ)) 7 (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33787/262144 : ℝ))) (35613594693/200000000000 : ℝ) (178067973471/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33787/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35613594693/200000000000 : ℝ) (178067973471/1000000000000 : ℝ) (147258496683/250000000000 : ℝ) (36814624171/62500000000 : ℝ) (421981010787/1000000000000 : ℝ) (84396202159/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33787/262144 : ℝ))) 1 (147258496683/250000000000 : ℝ) (36814624171/62500000000 : ℝ) (421981010787/1000000000000 : ℝ) (84396202159/200000000000 : ℝ) (505507498759/1000000000000 : ℝ) (252753749383/500000000000 : ℝ) (498559080861/1000000000000 : ℝ) (124639770217/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33787/262144 : ℝ))) 2 (505507498759/1000000000000 : ℝ) (252753749383/500000000000 : ℝ) (498559080861/1000000000000 : ℝ) (124639770217/250000000000 : ℝ) (50203328981/100000000000 : ℝ) (502033289817/1000000000000 : ℝ) (502021268423/1000000000000 : ℝ) (502021268431/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33787/262144 : ℝ))) 3 (50203328981/100000000000 : ℝ) (502033289817/1000000000000 : ℝ) (502021268423/1000000000000 : ℝ) (502021268431/1000000000000 : ℝ) (125506819779/250000000000 : ℝ) (125506819781/250000000000 : ℝ) (12550681977/25000000000 : ℝ) (502027279089/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33787/262144 : ℝ))) 4 (125506819779/250000000000 : ℝ) (125506819781/250000000000 : ℝ) (12550681977/25000000000 : ℝ) (502027279089/1000000000000 : ℝ) (251013639549/500000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33787/262144 : ℝ))) 5 (251013639549/500000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33787/262144 : ℝ))) 6 (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33787/262144 : ℝ))) 7 (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33787/262144 : ℝ)) hmem 8 (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33787/262144 : ℝ))) hcmem 8 (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33787/262144 : ℝ)) (247998250519/250000000000 : ℝ) (991993002079/1000000000000 : ℝ) (502027279097/1000000000000 : ℝ) (502027279107/1000000000000 : ℝ) (158989550189/200000000000 : ℝ) (198736937741/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1354_exp_lower
  have heNumeric : (2054905727031/1000000000000 : ℝ)/4 ≤ Real.exp (-21314060452723/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905727031/1000000000000 : ℝ)/4 ≤ Real.exp ((16893/131072 : ℝ)-(198736937741/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16893/131072 : ℝ) (33787/262144 : ℝ) (198736937741/250000000000 : ℝ) (2054905727031/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1355; no trusted numerical premise.
theorem cover8_leaf1355_exp_radius : (997988104842025907/1000000000000000000 : ℝ) ≤ Real.exp ((-8447/524288 : ℝ)/8) ∧ Real.exp ((-8447/524288 : ℝ)/8) ≤ (249497026210506477/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8447/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1355_exp_lower : (920113685326235751/1000000000000000000 : ℝ) ≤ Real.exp ((-42628119330069/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628119330069/64000000000000 : ℝ)/8) ≤ (115014210665779469/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628119330069/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1355_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452888807/500000000000 : ℝ) ≤ 4*Real.exp (33787/262144 : ℝ)*Real.exp (-mu (radius 8 (8447/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452888807/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8447/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1355_exp_radius
  have hrNumeric : (984017720059/1000000000000 : ℝ) ≤ Real.exp (-8447/524288 : ℝ) ∧ Real.exp (-8447/524288 : ℝ) ≤ (49200886003/50000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984017720059/1000000000000 : ℝ) ≤ (radius 8 (8447/65536 : ℝ)) ∧ (radius 8 (8447/65536 : ℝ)) ≤ (49200886003/50000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8447/65536 : ℝ)) (984017720059/1000000000000 : ℝ) (49200886003/50000000000 : ℝ) (178070566371/1000000000000 : ℝ) (89035283189/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8447/65536 : ℝ)) (984017720059/1000000000000 : ℝ) (49200886003/50000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8447/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984017720059/1000000000000 : ℝ) (49200886003/50000000000 : ℝ) (992008860029/1000000000000 : ℝ) (99200886003/100000000000 : ℝ) (495988336571/500000000000 : ℝ) (123997084143/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8447/65536 : ℝ)) 1 (992008860029/1000000000000 : ℝ) (99200886003/100000000000 : ℝ) (495988336571/500000000000 : ℝ) (123997084143/125000000000 : ℝ) (198398553317/200000000000 : ℝ) (991992766587/1000000000000 : ℝ) (495996383227/500000000000 : ℝ) (991992766457/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8447/65536 : ℝ)) 2 (198398553317/200000000000 : ℝ) (991992766587/1000000000000 : ℝ) (495996383227/500000000000 : ℝ) (991992766457/1000000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8447/65536 : ℝ)) 3 (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8447/65536 : ℝ)) 4 (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8447/65536 : ℝ)) 5 (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8447/65536 : ℝ)) 6 (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8447/65536 : ℝ)) 7 (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8447/65536 : ℝ))) (178070566371/1000000000000 : ℝ) (89035283189/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8447/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178070566371/1000000000000 : ℝ) (89035283189/500000000000 : ℝ) (117807056637/200000000000 : ℝ) (589035283189/1000000000000 : ℝ) (421984083077/1000000000000 : ℝ) (421984083087/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8447/65536 : ℝ))) 1 (117807056637/200000000000 : ℝ) (589035283189/1000000000000 : ℝ) (421984083077/1000000000000 : ℝ) (421984083087/1000000000000 : ℝ) (505509683131/1000000000000 : ℝ) (252754841569/500000000000 : ℝ) (31160090277/62500000000 : ℝ) (498561444441/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8447/65536 : ℝ))) 2 (505509683131/1000000000000 : ℝ) (252754841569/500000000000 : ℝ) (31160090277/62500000000 : ℝ) (498561444441/1000000000000 : ℝ) (502035563781/1000000000000 : ℝ) (50203556379/100000000000 : ℝ) (502023543069/1000000000000 : ℝ) (251011771539/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8447/65536 : ℝ))) 3 (502035563781/1000000000000 : ℝ) (50203556379/100000000000 : ℝ) (502023543069/1000000000000 : ℝ) (251011771539/500000000000 : ℝ) (20081182137/40000000000 : ℝ) (251014776717/500000000000 : ℝ) (502029553389/1000000000000 : ℝ) (502029553399/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8447/65536 : ℝ))) 4 (20081182137/40000000000 : ℝ) (251014776717/500000000000 : ℝ) (502029553389/1000000000000 : ℝ) (502029553399/1000000000000 : ℝ) (502029553407/1000000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8447/65536 : ℝ))) 5 (502029553407/1000000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8447/65536 : ℝ))) 6 (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8447/65536 : ℝ))) 7 (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8447/65536 : ℝ)) hmem 8 (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8447/65536 : ℝ))) hcmem 8 (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8447/65536 : ℝ)) (991992766519/1000000000000 : ℝ) (495996383261/500000000000 : ℝ) (251014776703/500000000000 : ℝ) (502029553417/1000000000000 : ℝ) (31798061641/40000000000 : ℝ) (397475770523/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1355_exp_lower
  have heNumeric : (1027452888807/500000000000 : ℝ)/4 ≤ Real.exp (-42628119330069/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452888807/500000000000 : ℝ)/4 ≤ Real.exp ((33787/262144 : ℝ)-(397475770523/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33787/262144 : ℝ) (8447/65536 : ℝ) (397475770523/500000000000 : ℝ) (1027452888807/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1356; no trusted numerical premise.
theorem cover8_leaf1356_exp_radius : (997988045357301201/1000000000000000000 : ℝ) ≤ Real.exp ((-33789/2097152 : ℝ)/8) ∧ Real.exp ((-33789/2097152 : ℝ)/8) ≤ (498994022678650601/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33789/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1356_exp_lower : (230028422041549299/250000000000000000 : ℝ) ≤ Real.exp ((-10657029437441/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657029437441/16000000000000 : ℝ)/8) ≤ (920113688166197197/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657029437441/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1356_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452914177/500000000000 : ℝ) ≤ 4*Real.exp (8447/65536 : ℝ)*Real.exp (-mu (radius 8 (33789/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452914177/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33789/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1356_exp_radius
  have hrNumeric : (984017250843/1000000000000 : ℝ) ≤ Real.exp (-33789/2097152 : ℝ) ∧ Real.exp (-33789/2097152 : ℝ) ≤ (246004312711/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984017250843/1000000000000 : ℝ) ≤ (radius 8 (33789/262144 : ℝ)) ∧ (radius 8 (33789/262144 : ℝ)) ≤ (246004312711/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33789/262144 : ℝ)) (984017250843/1000000000000 : ℝ) (246004312711/250000000000 : ℝ) (178073159239/1000000000000 : ℝ) (35614631849/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33789/262144 : ℝ)) (984017250843/1000000000000 : ℝ) (246004312711/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33789/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984017250843/1000000000000 : ℝ) (246004312711/250000000000 : ℝ) (992008625421/1000000000000 : ℝ) (496004312711/500000000000 : ℝ) (247994109159/250000000000 : ℝ) (495988218319/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33789/262144 : ℝ)) 1 (992008625421/1000000000000 : ℝ) (496004312711/500000000000 : ℝ) (247994109159/250000000000 : ℝ) (495988218319/500000000000 : ℝ) (247998132757/250000000000 : ℝ) (99199253103/100000000000 : ℝ) (991992530897/1000000000000 : ℝ) (9919925309/10000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33789/262144 : ℝ)) 2 (247998132757/250000000000 : ℝ) (99199253103/100000000000 : ℝ) (991992530897/1000000000000 : ℝ) (9919925309/10000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33789/262144 : ℝ)) 3 (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33789/262144 : ℝ)) 4 (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33789/262144 : ℝ)) 5 (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33789/262144 : ℝ)) 6 (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33789/262144 : ℝ)) 7 (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33789/262144 : ℝ))) (178073159239/1000000000000 : ℝ) (35614631849/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33789/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178073159239/1000000000000 : ℝ) (35614631849/200000000000 : ℝ) (589036579619/1000000000000 : ℝ) (589036579623/1000000000000 : ℝ) (4219871553/10000000000 : ℝ) (421987155309/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33789/262144 : ℝ))) 1 (589036579619/1000000000000 : ℝ) (589036579623/1000000000000 : ℝ) (4219871553/10000000000 : ℝ) (421987155309/1000000000000 : ℝ) (505511867459/1000000000000 : ℝ) (252755933733/500000000000 : ℝ) (498563807953/1000000000000 : ℝ) (498563807961/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33789/262144 : ℝ))) 2 (505511867459/1000000000000 : ℝ) (252755933733/500000000000 : ℝ) (498563807953/1000000000000 : ℝ) (498563807961/1000000000000 : ℝ) (251018918853/500000000000 : ℝ) (251018918857/500000000000 : ℝ) (125506454417/250000000000 : ℝ) (502025817677/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33789/262144 : ℝ))) 3 (251018918853/500000000000 : ℝ) (251018918857/500000000000 : ℝ) (125506454417/250000000000 : ℝ) (502025817677/1000000000000 : ℝ) (502031827687/1000000000000 : ℝ) (31376989231/62500000000 : ℝ) (502031827651/1000000000000 : ℝ) (25101591383/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33789/262144 : ℝ))) 4 (502031827687/1000000000000 : ℝ) (31376989231/62500000000 : ℝ) (502031827651/1000000000000 : ℝ) (25101591383/50000000000 : ℝ) (502031827669/1000000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33789/262144 : ℝ))) 5 (502031827669/1000000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33789/262144 : ℝ))) 6 (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33789/262144 : ℝ))) 7 (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33789/262144 : ℝ)) hmem 8 (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33789/262144 : ℝ))) hcmem 8 (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33789/262144 : ℝ)) (495996265481/500000000000 : ℝ) (198398506193/200000000000 : ℝ) (125507956917/250000000000 : ℝ) (251015913839/500000000000 : ℝ) (99369416379/125000000000 : ℝ) (794955331051/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1356_exp_lower
  have heNumeric : (1027452914177/500000000000 : ℝ)/4 ≤ Real.exp (-10657029437441/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452914177/500000000000 : ℝ)/4 ≤ Real.exp ((8447/65536 : ℝ)-(794955331051/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8447/65536 : ℝ) (33789/262144 : ℝ) (794955331051/1000000000000 : ℝ) (1027452914177/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1357; no trusted numerical premise.
theorem cover8_leaf1357_exp_radius : (24949699646814501/25000000000000000 : ℝ) ≤ Real.exp ((-16895/1048576 : ℝ)/8) ∧ Real.exp ((-16895/1048576 : ℝ)/8) ≤ (997987985872580041/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16895/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1357_exp_lower : (920113691014669701/1000000000000000000 : ℝ) ≤ Real.exp ((-42628116164723/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628116164723/64000000000000 : ℝ)/8) ≤ (460056845507334851/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628116164723/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1357_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452939623/500000000000 : ℝ) ≤ 4*Real.exp (33789/262144 : ℝ)*Real.exp (-mu (radius 8 (16895/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452939623/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16895/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1357_exp_radius
  have hrNumeric : (984016781627/1000000000000 : ℝ) ≤ Real.exp (-16895/1048576 : ℝ) ∧ Real.exp (-16895/1048576 : ℝ) ≤ (246004195407/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984016781627/1000000000000 : ℝ) ≤ (radius 8 (16895/131072 : ℝ)) ∧ (radius 8 (16895/131072 : ℝ)) ≤ (246004195407/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16895/131072 : ℝ)) (984016781627/1000000000000 : ℝ) (246004195407/250000000000 : ℝ) (178075752067/1000000000000 : ℝ) (89037876037/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16895/131072 : ℝ)) (984016781627/1000000000000 : ℝ) (246004195407/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16895/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984016781627/1000000000000 : ℝ) (246004195407/250000000000 : ℝ) (992008390813/1000000000000 : ℝ) (496004195407/500000000000 : ℝ) (991976200131/1000000000000 : ℝ) (247994050033/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16895/131072 : ℝ)) 1 (992008390813/1000000000000 : ℝ) (496004195407/500000000000 : ℝ) (991976200131/1000000000000 : ℝ) (247994050033/250000000000 : ℝ) (61999518467/62500000000 : ℝ) (991992295473/1000000000000 : ℝ) (991992295341/1000000000000 : ℝ) (991992295343/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16895/131072 : ℝ)) 2 (61999518467/62500000000 : ℝ) (991992295473/1000000000000 : ℝ) (991992295341/1000000000000 : ℝ) (991992295343/1000000000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16895/131072 : ℝ)) 3 (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16895/131072 : ℝ)) 4 (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16895/131072 : ℝ)) 5 (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16895/131072 : ℝ)) 6 (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16895/131072 : ℝ)) 7 (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16895/131072 : ℝ))) (178075752067/1000000000000 : ℝ) (89037876037/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16895/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178075752067/1000000000000 : ℝ) (89037876037/500000000000 : ℝ) (589037876033/1000000000000 : ℝ) (589037876037/1000000000000 : ℝ) (210995113727/500000000000 : ℝ) (421990227463/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16895/131072 : ℝ))) 1 (589037876033/1000000000000 : ℝ) (589037876037/1000000000000 : ℝ) (210995113727/500000000000 : ℝ) (421990227463/1000000000000 : ℝ) (505514051743/1000000000000 : ℝ) (2022056207/4000000000 : ℝ) (498566171421/1000000000000 : ℝ) (498566171429/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16895/131072 : ℝ))) 2 (505514051743/1000000000000 : ℝ) (2022056207/4000000000 : ℝ) (498566171421/1000000000000 : ℝ) (498566171429/1000000000000 : ℝ) (251020055791/500000000000 : ℝ) (50204011159/100000000000 : ℝ) (251014046109/500000000000 : ℝ) (502028092227/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16895/131072 : ℝ))) 3 (251020055791/500000000000 : ℝ) (50204011159/100000000000 : ℝ) (251014046109/500000000000 : ℝ) (502028092227/1000000000000 : ℝ) (5020341019/10000000000 : ℝ) (502034101909/1000000000000 : ℝ) (62754262733/125000000000 : ℝ) (502034101873/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16895/131072 : ℝ))) 4 (5020341019/10000000000 : ℝ) (502034101909/1000000000000 : ℝ) (62754262733/125000000000 : ℝ) (502034101873/1000000000000 : ℝ) (251017050941/500000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16895/131072 : ℝ))) 5 (251017050941/500000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16895/131072 : ℝ))) 6 (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16895/131072 : ℝ))) 7 (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16895/131072 : ℝ)) hmem 8 (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16895/131072 : ℝ))) hcmem 8 (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16895/131072 : ℝ)) (495996147703/500000000000 : ℝ) (61999518463/62500000000 : ℝ) (502034101881/1000000000000 : ℝ) (502034101891/1000000000000 : ℝ) (794959120963/1000000000000 : ℝ) (397479560491/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1357_exp_lower
  have heNumeric : (1027452939623/500000000000 : ℝ)/4 ≤ Real.exp (-42628116164723/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452939623/500000000000 : ℝ)/4 ≤ Real.exp ((33789/262144 : ℝ)-(397479560491/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33789/262144 : ℝ) (16895/131072 : ℝ) (397479560491/500000000000 : ℝ) (1027452939623/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1358; no trusted numerical premise.
theorem cover8_leaf1358_exp_radius : (39919517055514497/40000000000000000 : ℝ) ≤ Real.exp ((-33791/2097152 : ℝ)/8) ∧ Real.exp ((-33791/2097152 : ℝ)/8) ≤ (498993963193931213/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33791/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1358_exp_lower : (920113693871423239/1000000000000000000 : ℝ) ≤ Real.exp ((-21314057287537/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314057287537/32000000000000 : ℝ)/8) ≤ (23002842346785581/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314057287537/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1358_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452965143/500000000000 : ℝ) ≤ 4*Real.exp (16895/131072 : ℝ)*Real.exp (-mu (radius 8 (33791/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452965143/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33791/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1358_exp_radius
  have hrNumeric : (984016312411/1000000000000 : ℝ) ≤ Real.exp (-33791/2097152 : ℝ) ∧ Real.exp (-33791/2097152 : ℝ) ≤ (246004078103/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984016312411/1000000000000 : ℝ) ≤ (radius 8 (33791/262144 : ℝ)) ∧ (radius 8 (33791/262144 : ℝ)) ≤ (246004078103/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33791/262144 : ℝ)) (984016312411/1000000000000 : ℝ) (246004078103/250000000000 : ℝ) (178078344857/1000000000000 : ℝ) (178078344863/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33791/262144 : ℝ)) (984016312411/1000000000000 : ℝ) (246004078103/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33791/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984016312411/1000000000000 : ℝ) (246004078103/250000000000 : ℝ) (198401631241/200000000000 : ℝ) (496004078103/500000000000 : ℝ) (7935807709/8000000000 : ℝ) (991975963627/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33791/262144 : ℝ)) 1 (198401631241/200000000000 : ℝ) (496004078103/500000000000 : ℝ) (7935807709/8000000000 : ℝ) (991975963627/1000000000000 : ℝ) (198398411983/200000000000 : ℝ) (991992059917/1000000000000 : ℝ) (123999007473/125000000000 : ℝ) (495996029893/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33791/262144 : ℝ)) 2 (198398411983/200000000000 : ℝ) (991992059917/1000000000000 : ℝ) (123999007473/125000000000 : ℝ) (495996029893/500000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33791/262144 : ℝ)) 3 (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33791/262144 : ℝ)) 4 (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33791/262144 : ℝ)) 5 (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33791/262144 : ℝ)) 6 (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33791/262144 : ℝ)) 7 (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33791/262144 : ℝ))) (178078344857/1000000000000 : ℝ) (178078344863/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33791/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178078344857/1000000000000 : ℝ) (178078344863/1000000000000 : ℝ) (147259793107/250000000000 : ℝ) (36814948277/62500000000 : ℝ) (21099664977/50000000000 : ℝ) (105498324887/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33791/262144 : ℝ))) 1 (147259793107/250000000000 : ℝ) (36814948277/62500000000 : ℝ) (21099664977/50000000000 : ℝ) (105498324887/250000000000 : ℝ) (31594764749/62500000000 : ℝ) (50551623599/100000000000 : ℝ) (249284267419/500000000000 : ℝ) (249284267423/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33791/262144 : ℝ))) 2 (31594764749/62500000000 : ℝ) (50551623599/100000000000 : ℝ) (249284267419/500000000000 : ℝ) (249284267423/500000000000 : ℝ) (502042385411/1000000000000 : ℝ) (251021192709/500000000000 : ℝ) (251015183361/500000000000 : ℝ) (50203036673/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33791/262144 : ℝ))) 3 (502042385411/1000000000000 : ℝ) (251021192709/500000000000 : ℝ) (251015183361/500000000000 : ℝ) (50203036673/100000000000 : ℝ) (251018188033/500000000000 : ℝ) (251018188037/500000000000 : ℝ) (50203637603/100000000000 : ℝ) (502036376039/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33791/262144 : ℝ))) 4 (251018188033/500000000000 : ℝ) (251018188037/500000000000 : ℝ) (50203637603/100000000000 : ℝ) (502036376039/1000000000000 : ℝ) (31377273503/62500000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33791/262144 : ℝ))) 5 (31377273503/62500000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33791/262144 : ℝ))) 6 (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33791/262144 : ℝ))) 7 (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33791/262144 : ℝ)) hmem 8 (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33791/262144 : ℝ))) hcmem 8 (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33791/262144 : ℝ)) (991992059849/1000000000000 : ℝ) (247998014963/250000000000 : ℝ) (502036376047/1000000000000 : ℝ) (502036376057/1000000000000 : ℝ) (794962910821/1000000000000 : ℝ) (794962910841/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1358_exp_lower
  have heNumeric : (1027452965143/500000000000 : ℝ)/4 ≤ Real.exp (-21314057287537/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452965143/500000000000 : ℝ)/4 ≤ Real.exp ((16895/131072 : ℝ)-(794962910841/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16895/131072 : ℝ) (33791/262144 : ℝ) (794962910841/1000000000000 : ℝ) (1027452965143/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1359; no trusted numerical premise.
theorem cover8_leaf1359_exp_radius : (199597573380629671/200000000000000000 : ℝ) ≤ Real.exp ((-33/2048 : ℝ)/8) ∧ Real.exp ((-33/2048 : ℝ)/8) ≤ (249496966725787089/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1359_exp_lower : (920113696737952993/1000000000000000000 : ℝ) ≤ Real.exp ((-8525622595997/12800000000000 : ℝ)/8) ∧ Real.exp ((-8525622595997/12800000000000 : ℝ)/8) ≤ (460056848368976497/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8525622595997/12800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1359_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054905981501/1000000000000 : ℝ) ≤ 4*Real.exp (33791/262144 : ℝ)*Real.exp (-mu (radius 8 (33/256 : ℝ))) ∧ (20549/10000 : ℝ) < (2054905981501/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1359_exp_radius
  have hrNumeric : (246003960799/250000000000 : ℝ) ≤ Real.exp (-33/2048 : ℝ) ∧ Real.exp (-33/2048 : ℝ) ≤ (984015843197/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246003960799/250000000000 : ℝ) ≤ (radius 8 (33/256 : ℝ)) ∧ (radius 8 (33/256 : ℝ)) ≤ (984015843197/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33/256 : ℝ)) (246003960799/250000000000 : ℝ) (984015843197/1000000000000 : ℝ) (89040468801/500000000000 : ℝ) (22260117201/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33/256 : ℝ)) (246003960799/250000000000 : ℝ) (984015843197/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246003960799/250000000000 : ℝ) (984015843197/1000000000000 : ℝ) (496003960799/500000000000 : ℝ) (992007921599/1000000000000 : ℝ) (12399696589/12500000000 : ℝ) (991975727121/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33/256 : ℝ)) 1 (496003960799/500000000000 : ℝ) (992007921599/1000000000000 : ℝ) (12399696589/12500000000 : ℝ) (991975727121/1000000000000 : ℝ) (991991824359/1000000000000 : ℝ) (24799795609/25000000000 : ℝ) (247997956057/250000000000 : ℝ) (99199182423/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33/256 : ℝ)) 2 (991991824359/1000000000000 : ℝ) (24799795609/25000000000 : ℝ) (247997956057/250000000000 : ℝ) (99199182423/100000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33/256 : ℝ)) 3 (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33/256 : ℝ)) 4 (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33/256 : ℝ)) 5 (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33/256 : ℝ)) 6 (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33/256 : ℝ)) 7 (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33/256 : ℝ))) (89040468801/500000000000 : ℝ) (22260117201/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89040468801/500000000000 : ℝ) (22260117201/125000000000 : ℝ) (589040468801/1000000000000 : ℝ) (147260117201/250000000000 : ℝ) (8439927431/20000000000 : ℝ) (210998185779/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33/256 : ℝ))) 1 (589040468801/1000000000000 : ℝ) (147260117201/250000000000 : ℝ) (8439927431/20000000000 : ℝ) (210998185779/500000000000 : ℝ) (20220736807/40000000000 : ℝ) (505518420181/1000000000000 : ℝ) (249285449099/500000000000 : ℝ) (99714179641/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33/256 : ℝ))) 2 (20220736807/40000000000 : ℝ) (505518420181/1000000000000 : ℝ) (249285449099/500000000000 : ℝ) (99714179641/200000000000 : ℝ) (251022329593/500000000000 : ℝ) (502044659193/1000000000000 : ℝ) (125508160293/250000000000 : ℝ) (502032641179/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33/256 : ℝ))) 3 (251022329593/500000000000 : ℝ) (502044659193/1000000000000 : ℝ) (125508160293/250000000000 : ℝ) (502032641179/1000000000000 : ℝ) (502038650179/1000000000000 : ℝ) (251019325093/500000000000 : ℝ) (502038650143/1000000000000 : ℝ) (502038650151/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33/256 : ℝ))) 4 (502038650179/1000000000000 : ℝ) (251019325093/500000000000 : ℝ) (502038650143/1000000000000 : ℝ) (502038650151/1000000000000 : ℝ) (502038650161/1000000000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33/256 : ℝ))) 5 (502038650161/1000000000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33/256 : ℝ))) 6 (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33/256 : ℝ))) 7 (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33/256 : ℝ)) hmem 8 (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33/256 : ℝ))) hcmem 8 (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33/256 : ℝ)) (991991824293/1000000000000 : ℝ) (198398364859/200000000000 : ℝ) (6275483127/12500000000 : ℝ) (502038650169/1000000000000 : ℝ) (397483350299/500000000000 : ℝ) (158993340123/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1359_exp_lower
  have heNumeric : (2054905981501/1000000000000 : ℝ)/4 ≤ Real.exp (-8525622595997/12800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054905981501/1000000000000 : ℝ)/4 ≤ Real.exp ((33791/262144 : ℝ)-(158993340123/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33791/262144 : ℝ) (33/256 : ℝ) (158993340123/200000000000 : ℝ) (2054905981501/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1360; no trusted numerical premise.
theorem cover8_leaf1360_exp_radius : (997987807418437831/1000000000000000000 : ℝ) ≤ Real.exp ((-33793/2097152 : ℝ)/8) ∧ Real.exp ((-33793/2097152 : ℝ)/8) ≤ (124748475927304729/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33793/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1360_exp_lower : (920113699612763779/1000000000000000000 : ℝ) ≤ Real.exp ((-666064240317/1000000000000 : ℝ)/8) ∧ Real.exp ((-666064240317/1000000000000 : ℝ)/8) ≤ (46005684980638189/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666064240317/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1360_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64215813527/31250000000 : ℝ) ≤ 4*Real.exp (33/256 : ℝ)*Real.exp (-mu (radius 8 (33793/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (64215813527/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33793/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1360_exp_radius
  have hrNumeric : (984015373981/1000000000000 : ℝ) ≤ Real.exp (-33793/2097152 : ℝ) ∧ Real.exp (-33793/2097152 : ℝ) ≤ (492007686991/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984015373981/1000000000000 : ℝ) ≤ (radius 8 (33793/262144 : ℝ)) ∧ (radius 8 (33793/262144 : ℝ)) ≤ (492007686991/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33793/262144 : ℝ)) (984015373981/1000000000000 : ℝ) (492007686991/500000000000 : ℝ) (44520882577/250000000000 : ℝ) (89041765157/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33793/262144 : ℝ)) (984015373981/1000000000000 : ℝ) (492007686991/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33793/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984015373981/1000000000000 : ℝ) (492007686991/500000000000 : ℝ) (99200768699/100000000000 : ℝ) (992007686991/1000000000000 : ℝ) (198395098123/200000000000 : ℝ) (123996936327/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33793/262144 : ℝ)) 1 (99200768699/100000000000 : ℝ) (992007686991/1000000000000 : ℝ) (198395098123/200000000000 : ℝ) (123996936327/125000000000 : ℝ) (495995794401/500000000000 : ℝ) (247997897201/250000000000 : ℝ) (991991588671/1000000000000 : ℝ) (991991588673/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33793/262144 : ℝ)) 2 (495995794401/500000000000 : ℝ) (247997897201/250000000000 : ℝ) (991991588671/1000000000000 : ℝ) (991991588673/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33793/262144 : ℝ)) 3 (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33793/262144 : ℝ)) 4 (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33793/262144 : ℝ)) 5 (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33793/262144 : ℝ)) 6 (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33793/262144 : ℝ)) 7 (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33793/262144 : ℝ))) (44520882577/250000000000 : ℝ) (89041765157/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33793/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44520882577/250000000000 : ℝ) (89041765157/500000000000 : ℝ) (294520882577/500000000000 : ℝ) (589041765157/1000000000000 : ℝ) (105499860873/250000000000 : ℝ) (843998887/2000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33793/262144 : ℝ))) 1 (294520882577/500000000000 : ℝ) (589041765157/1000000000000 : ℝ) (105499860873/250000000000 : ℝ) (843998887/2000000000 : ℝ) (505520604323/1000000000000 : ℝ) (505520604329/1000000000000 : ℝ) (99714652301/200000000000 : ℝ) (62321657689/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33793/262144 : ℝ))) 2 (505520604323/1000000000000 : ℝ) (505520604329/1000000000000 : ℝ) (99714652301/200000000000 : ℝ) (62321657689/125000000000 : ℝ) (251023466457/500000000000 : ℝ) (502046932921/1000000000000 : ℝ) (502034915573/1000000000000 : ℝ) (502034915581/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33793/262144 : ℝ))) 3 (251023466457/500000000000 : ℝ) (502046932921/1000000000000 : ℝ) (502034915573/1000000000000 : ℝ) (502034915581/1000000000000 : ℝ) (502040924243/1000000000000 : ℝ) (502040924251/1000000000000 : ℝ) (502040924207/1000000000000 : ℝ) (62755115527/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33793/262144 : ℝ))) 4 (502040924243/1000000000000 : ℝ) (502040924251/1000000000000 : ℝ) (502040924207/1000000000000 : ℝ) (62755115527/125000000000 : ℝ) (20081636969/40000000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33793/262144 : ℝ))) 5 (20081636969/40000000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33793/262144 : ℝ))) 6 (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33793/262144 : ℝ))) 7 (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33793/262144 : ℝ)) hmem 8 (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33793/262144 : ℝ))) hcmem 8 (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33793/262144 : ℝ)) (7749934287/7812500000 : ℝ) (991991588739/1000000000000 : ℝ) (7844389441/15625000000 : ℝ) (251020462117/500000000000 : ℝ) (397485245149/500000000000 : ℝ) (794970490317/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1360_exp_lower
  have heNumeric : (64215813527/31250000000 : ℝ)/4 ≤ Real.exp (-666064240317/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64215813527/31250000000 : ℝ)/4 ≤ Real.exp ((33/256 : ℝ)-(794970490317/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33/256 : ℝ) (33793/262144 : ℝ) (794970490317/1000000000000 : ℝ) (64215813527/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1361; no trusted numerical premise.
theorem cover8_leaf1361_exp_radius : (249496936983432713/250000000000000000 : ℝ) ≤ Real.exp ((-16897/1048576 : ℝ)/8) ∧ Real.exp ((-16897/1048576 : ℝ)/8) ≤ (997987747933730853/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16897/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1361_exp_lower : (184022740499263131/200000000000000000 : ℝ) ≤ Real.exp ((-42628109775727/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628109775727/64000000000000 : ℝ)/8) ≤ (115014212812039457/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628109775727/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1361_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906084383/1000000000000 : ℝ) ≤ 4*Real.exp (33793/262144 : ℝ)*Real.exp (-mu (radius 8 (16897/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906084383/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16897/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1361_exp_radius
  have hrNumeric : (492007452383/500000000000 : ℝ) ≤ Real.exp (-16897/1048576 : ℝ) ∧ Real.exp (-16897/1048576 : ℝ) ≤ (984014904767/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492007452383/500000000000 : ℝ) ≤ (radius 8 (16897/131072 : ℝ)) ∧ (radius 8 (16897/131072 : ℝ)) ≤ (984014904767/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16897/131072 : ℝ)) (492007452383/500000000000 : ℝ) (984014904767/1000000000000 : ℝ) (7123444919/40000000000 : ℝ) (178086122981/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16897/131072 : ℝ)) (492007452383/500000000000 : ℝ) (984014904767/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16897/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492007452383/500000000000 : ℝ) (984014904767/1000000000000 : ℝ) (992007452383/1000000000000 : ℝ) (31000232887/31250000000 : ℝ) (991975254109/1000000000000 : ℝ) (991975254111/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16897/131072 : ℝ)) 1 (992007452383/1000000000000 : ℝ) (31000232887/31250000000 : ℝ) (991975254109/1000000000000 : ℝ) (991975254111/1000000000000 : ℝ) (495995676623/500000000000 : ℝ) (30999729789/31250000000 : ℝ) (198398270623/200000000000 : ℝ) (991991353117/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16897/131072 : ℝ)) 2 (495995676623/500000000000 : ℝ) (30999729789/31250000000 : ℝ) (198398270623/200000000000 : ℝ) (991991353117/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16897/131072 : ℝ)) 3 (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16897/131072 : ℝ)) 4 (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16897/131072 : ℝ)) 5 (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16897/131072 : ℝ)) 6 (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16897/131072 : ℝ)) 7 (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16897/131072 : ℝ))) (7123444919/40000000000 : ℝ) (178086122981/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16897/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (7123444919/40000000000 : ℝ) (178086122981/1000000000000 : ℝ) (589043061487/1000000000000 : ℝ) (589043061491/1000000000000 : ℝ) (84400503073/200000000000 : ℝ) (422002515373/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16897/131072 : ℝ))) 1 (589043061487/1000000000000 : ℝ) (589043061491/1000000000000 : ℝ) (84400503073/200000000000 : ℝ) (422002515373/1000000000000 : ℝ) (252761394213/500000000000 : ℝ) (31595174277/62500000000 : ℝ) (12464390619/25000000000 : ℝ) (7790244137/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16897/131072 : ℝ))) 2 (252761394213/500000000000 : ℝ) (31595174277/62500000000 : ℝ) (12464390619/25000000000 : ℝ) (7790244137/15625000000 : ℝ) (502049206593/1000000000000 : ℝ) (2510246033/5000000000 : ℝ) (502037189927/1000000000000 : ℝ) (100407437987/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16897/131072 : ℝ))) 3 (502049206593/1000000000000 : ℝ) (2510246033/5000000000 : ℝ) (502037189927/1000000000000 : ℝ) (100407437987/200000000000 : ℝ) (25102159913/50000000000 : ℝ) (125510799567/250000000000 : ℝ) (31377699889/62500000000 : ℝ) (62755399779/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16897/131072 : ℝ))) 4 (25102159913/50000000000 : ℝ) (125510799567/250000000000 : ℝ) (31377699889/62500000000 : ℝ) (62755399779/125000000000 : ℝ) (251021599121/500000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16897/131072 : ℝ))) 5 (251021599121/500000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16897/131072 : ℝ))) 6 (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16897/131072 : ℝ))) 7 (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16897/131072 : ℝ)) hmem 8 (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16897/131072 : ℝ))) hcmem 8 (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16897/131072 : ℝ)) (49599567659/50000000000 : ℝ) (991991353183/1000000000000 : ℝ) (502043198241/1000000000000 : ℝ) (2008172793/4000000000 : ℝ) (31798971197/40000000000 : ℝ) (794974279943/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1361_exp_lower
  have heNumeric : (2054906084383/1000000000000 : ℝ)/4 ≤ Real.exp (-42628109775727/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906084383/1000000000000 : ℝ)/4 ≤ Real.exp ((33793/262144 : ℝ)-(794974279943/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33793/262144 : ℝ) (16897/131072 : ℝ) (794974279943/1000000000000 : ℝ) (2054906084383/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1362; no trusted numerical premise.
theorem cover8_leaf1362_exp_radius : (997987688449027419/1000000000000000000 : ℝ) ≤ Real.exp ((-33795/2097152 : ℝ)/8) ∧ Real.exp ((-33795/2097152 : ℝ)/8) ≤ (49899384422451371/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33795/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1362_exp_lower : (920113705388148563/1000000000000000000 : ℝ) ≤ Real.exp ((-21314054083279/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314054083279/32000000000000 : ℝ)/8) ≤ (230028426347037141/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314054083279/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1362_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (41098122721/20000000000 : ℝ) ≤ 4*Real.exp (16897/131072 : ℝ)*Real.exp (-mu (radius 8 (33795/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (41098122721/20000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33795/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1362_exp_radius
  have hrNumeric : (984014435551/1000000000000 : ℝ) ≤ Real.exp (-33795/2097152 : ℝ) ∧ Real.exp (-33795/2097152 : ℝ) ≤ (30750451111/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984014435551/1000000000000 : ℝ) ≤ (radius 8 (33795/262144 : ℝ)) ∧ (radius 8 (33795/262144 : ℝ)) ≤ (30750451111/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33795/262144 : ℝ)) (984014435551/1000000000000 : ℝ) (30750451111/31250000000 : ℝ) (178088715603/1000000000000 : ℝ) (178088715609/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33795/262144 : ℝ)) (984014435551/1000000000000 : ℝ) (30750451111/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33795/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984014435551/1000000000000 : ℝ) (30750451111/31250000000 : ℝ) (39680288711/40000000000 : ℝ) (62000451111/62500000000 : ℝ) (247993754401/250000000000 : ℝ) (198395003521/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33795/262144 : ℝ)) 1 (39680288711/40000000000 : ℝ) (62000451111/62500000000 : ℝ) (247993754401/250000000000 : ℝ) (198395003521/200000000000 : ℝ) (991991117689/1000000000000 : ℝ) (991991117691/1000000000000 : ℝ) (495995558779/500000000000 : ℝ) (24799777939/25000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33795/262144 : ℝ)) 2 (991991117689/1000000000000 : ℝ) (991991117691/1000000000000 : ℝ) (495995558779/500000000000 : ℝ) (24799777939/25000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33795/262144 : ℝ)) 3 (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33795/262144 : ℝ)) 4 (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33795/262144 : ℝ)) 5 (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33795/262144 : ℝ)) 6 (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33795/262144 : ℝ)) 7 (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33795/262144 : ℝ))) (178088715603/1000000000000 : ℝ) (178088715609/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33795/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178088715603/1000000000000 : ℝ) (178088715609/1000000000000 : ℝ) (589044357801/1000000000000 : ℝ) (117808871561/200000000000 : ℝ) (42200558717/100000000000 : ℝ) (211002793589/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33795/262144 : ℝ))) 1 (589044357801/1000000000000 : ℝ) (117808871561/200000000000 : ℝ) (42200558717/100000000000 : ℝ) (211002793589/500000000000 : ℝ) (101104994497/200000000000 : ℝ) (126381243123/250000000000 : ℝ) (124644496991/250000000000 : ℝ) (124644496993/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33795/262144 : ℝ))) 2 (101104994497/200000000000 : ℝ) (126381243123/250000000000 : ℝ) (124644496991/250000000000 : ℝ) (124644496993/250000000000 : ℝ) (15689108757/31250000000 : ℝ) (62756435029/125000000000 : ℝ) (62754933029/125000000000 : ℝ) (502039464241/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33795/262144 : ℝ))) 3 (15689108757/31250000000 : ℝ) (62756435029/125000000000 : ℝ) (62754933029/125000000000 : ℝ) (502039464241/1000000000000 : ℝ) (125511368057/250000000000 : ℝ) (502045472237/1000000000000 : ℝ) (7844460503/15625000000 : ℝ) (502045472201/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33795/262144 : ℝ))) 4 (125511368057/250000000000 : ℝ) (502045472237/1000000000000 : ℝ) (7844460503/15625000000 : ℝ) (502045472201/1000000000000 : ℝ) (50204547221/100000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33795/262144 : ℝ))) 5 (50204547221/100000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33795/262144 : ℝ))) 6 (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33795/262144 : ℝ))) 7 (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33795/262144 : ℝ)) hmem 8 (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33795/262144 : ℝ))) hcmem 8 (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33795/262144 : ℝ)) (991991117623/1000000000000 : ℝ) (495995558813/500000000000 : ℝ) (502045472209/1000000000000 : ℝ) (502045472219/1000000000000 : ℝ) (397489034739/500000000000 : ℝ) (794978069497/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1362_exp_lower
  have heNumeric : (41098122721/20000000000 : ℝ)/4 ≤ Real.exp (-21314054083279/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (41098122721/20000000000 : ℝ)/4 ≤ Real.exp ((16897/131072 : ℝ)-(794978069497/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16897/131072 : ℝ) (33795/262144 : ℝ) (794978069497/1000000000000 : ℝ) (41098122721/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1363; no trusted numerical premise.
theorem cover8_leaf1363_exp_radius : (249496907241081883/250000000000000000 : ℝ) ≤ Real.exp ((-8449/524288 : ℝ)/8) ∧ Real.exp ((-8449/524288 : ℝ)/8) ≤ (997987628964327533/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8449/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1363_exp_lower : (920113708289527659/1000000000000000000 : ℝ) ≤ Real.exp ((-42628106552077/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628106552077/64000000000000 : ℝ)/8) ≤ (46005685414476383/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628106552077/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1363_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431636743/62500000000 : ℝ) ≤ 4*Real.exp (33795/262144 : ℝ)*Real.exp (-mu (radius 8 (8449/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (128431636743/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8449/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1363_exp_radius
  have hrNumeric : (984013966337/1000000000000 : ℝ) ≤ Real.exp (-8449/524288 : ℝ) ∧ Real.exp (-8449/524288 : ℝ) ≤ (492006983169/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984013966337/1000000000000 : ℝ) ≤ (radius 8 (8449/65536 : ℝ)) ∧ (radius 8 (8449/65536 : ℝ)) ≤ (492006983169/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8449/65536 : ℝ)) (984013966337/1000000000000 : ℝ) (492006983169/500000000000 : ℝ) (178091308187/1000000000000 : ℝ) (178091308193/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8449/65536 : ℝ)) (984013966337/1000000000000 : ℝ) (492006983169/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8449/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984013966337/1000000000000 : ℝ) (492006983169/500000000000 : ℝ) (1937513639/1953125000 : ℝ) (992006983169/1000000000000 : ℝ) (991974781099/1000000000000 : ℝ) (9919747811/10000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8449/65536 : ℝ)) 1 (1937513639/1953125000 : ℝ) (992006983169/1000000000000 : ℝ) (991974781099/1000000000000 : ℝ) (9919747811/10000000000 : ℝ) (991990882133/1000000000000 : ℝ) (198398176427/200000000000 : ℝ) (495995441001/500000000000 : ℝ) (247997720501/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8449/65536 : ℝ)) 2 (991990882133/1000000000000 : ℝ) (198398176427/200000000000 : ℝ) (495995441001/500000000000 : ℝ) (247997720501/250000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8449/65536 : ℝ)) 3 (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8449/65536 : ℝ)) 4 (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8449/65536 : ℝ)) 5 (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8449/65536 : ℝ)) 6 (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8449/65536 : ℝ)) 7 (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8449/65536 : ℝ))) (178091308187/1000000000000 : ℝ) (178091308193/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8449/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178091308187/1000000000000 : ℝ) (178091308193/1000000000000 : ℝ) (589045654093/1000000000000 : ℝ) (589045654097/1000000000000 : ℝ) (4220086589/10000000000 : ℝ) (105502164727/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8449/65536 : ℝ))) 1 (589045654093/1000000000000 : ℝ) (589045654097/1000000000000 : ℝ) (4220086589/10000000000 : ℝ) (105502164727/250000000000 : ℝ) (31595447281/62500000000 : ℝ) (505527156503/1000000000000 : ℝ) (498580351111/1000000000000 : ℝ) (498580351119/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8449/65536 : ℝ))) 2 (31595447281/62500000000 : ℝ) (505527156503/1000000000000 : ℝ) (498580351111/1000000000000 : ℝ) (498580351119/1000000000000 : ℝ) (502053753803/1000000000000 : ℝ) (502053753811/1000000000000 : ℝ) (100408347697/200000000000 : ℝ) (251020869247/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8449/65536 : ℝ))) 3 (502053753803/1000000000000 : ℝ) (502053753811/1000000000000 : ℝ) (100408347697/200000000000 : ℝ) (251020869247/500000000000 : ℝ) (15688992067/31250000000 : ℝ) (502047746153/1000000000000 : ℝ) (125511936527/250000000000 : ℝ) (502047746117/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8449/65536 : ℝ))) 4 (15688992067/31250000000 : ℝ) (502047746153/1000000000000 : ℝ) (125511936527/250000000000 : ℝ) (502047746117/1000000000000 : ℝ) (251023873063/500000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8449/65536 : ℝ))) 5 (251023873063/500000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8449/65536 : ℝ))) 6 (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8449/65536 : ℝ))) 7 (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8449/65536 : ℝ)) hmem 8 (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8449/65536 : ℝ))) hcmem 8 (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8449/65536 : ℝ)) (991990882067/1000000000000 : ℝ) (99199088207/100000000000 : ℝ) (4016381969/8000000000 : ℝ) (100409549227/200000000000 : ℝ) (794981858949/1000000000000 : ℝ) (99372732371/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1363_exp_lower
  have heNumeric : (128431636743/62500000000 : ℝ)/4 ≤ Real.exp (-42628106552077/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431636743/62500000000 : ℝ)/4 ≤ Real.exp ((33795/262144 : ℝ)-(99372732371/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33795/262144 : ℝ) (8449/65536 : ℝ) (99372732371/125000000000 : ℝ) (128431636743/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1364; no trusted numerical premise.
theorem cover8_leaf1364_exp_radius : (99798756947963119/100000000000000000 : ℝ) ≤ Real.exp ((-33797/2097152 : ℝ)/8) ∧ Real.exp ((-33797/2097152 : ℝ)/8) ≤ (997987569479631191/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33797/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1364_exp_lower : (920113711198497703/1000000000000000000 : ℝ) ≤ Real.exp ((-10657026233343/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657026233343/16000000000000 : ℝ)/8) ≤ (115014213899812213/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657026233343/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1364_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906239861/1000000000000 : ℝ) ≤ 4*Real.exp (8449/65536 : ℝ)*Real.exp (-mu (radius 8 (33797/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906239861/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33797/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1364_exp_radius
  have hrNumeric : (492006748561/500000000000 : ℝ) ≤ Real.exp (-33797/2097152 : ℝ) ∧ Real.exp (-33797/2097152 : ℝ) ≤ (984013497123/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492006748561/500000000000 : ℝ) ≤ (radius 8 (33797/262144 : ℝ)) ∧ (radius 8 (33797/262144 : ℝ)) ≤ (984013497123/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33797/262144 : ℝ)) (492006748561/500000000000 : ℝ) (984013497123/1000000000000 : ℝ) (178093900737/1000000000000 : ℝ) (178093900743/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33797/262144 : ℝ)) (492006748561/500000000000 : ℝ) (984013497123/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33797/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492006748561/500000000000 : ℝ) (984013497123/1000000000000 : ℝ) (992006748561/1000000000000 : ℝ) (496003374281/500000000000 : ℝ) (991974544593/1000000000000 : ℝ) (198394908919/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33797/262144 : ℝ)) 1 (992006748561/1000000000000 : ℝ) (496003374281/500000000000 : ℝ) (991974544593/1000000000000 : ℝ) (198394908919/200000000000 : ℝ) (991990646577/1000000000000 : ℝ) (991990646579/1000000000000 : ℝ) (495995323223/500000000000 : ℝ) (61999415403/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33797/262144 : ℝ)) 2 (991990646577/1000000000000 : ℝ) (991990646579/1000000000000 : ℝ) (495995323223/500000000000 : ℝ) (61999415403/62500000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33797/262144 : ℝ)) 3 (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33797/262144 : ℝ)) 4 (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33797/262144 : ℝ)) 5 (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33797/262144 : ℝ)) 6 (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33797/262144 : ℝ)) 7 (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33797/262144 : ℝ))) (178093900737/1000000000000 : ℝ) (178093900743/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33797/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178093900737/1000000000000 : ℝ) (178093900743/1000000000000 : ℝ) (18407717199/31250000000 : ℝ) (147261737593/250000000000 : ℝ) (52751466321/125000000000 : ℝ) (26375733161/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33797/262144 : ℝ))) 1 (18407717199/31250000000 : ℝ) (147261737593/250000000000 : ℝ) (52751466321/125000000000 : ℝ) (26375733161/62500000000 : ℝ) (126382335117/250000000000 : ℝ) (252764670237/500000000000 : ℝ) (498582714211/1000000000000 : ℝ) (498582714219/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33797/262144 : ℝ))) 2 (126382335117/250000000000 : ℝ) (252764670237/500000000000 : ℝ) (498582714211/1000000000000 : ℝ) (498582714219/1000000000000 : ℝ) (502056027339/1000000000000 : ℝ) (502056027347/1000000000000 : ℝ) (100408802539/200000000000 : ℝ) (502044012703/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33797/262144 : ℝ))) 3 (502056027339/1000000000000 : ℝ) (502056027347/1000000000000 : ℝ) (100408802539/200000000000 : ℝ) (502044012703/1000000000000 : ℝ) (502050020017/1000000000000 : ℝ) (20082000801/40000000000 : ℝ) (502050019981/1000000000000 : ℝ) (50205001999/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33797/262144 : ℝ))) 4 (502050020017/1000000000000 : ℝ) (20082000801/40000000000 : ℝ) (502050019981/1000000000000 : ℝ) (50205001999/100000000000 : ℝ) (502050019999/1000000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33797/262144 : ℝ))) 5 (502050019999/1000000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33797/262144 : ℝ))) 6 (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33797/262144 : ℝ))) 7 (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33797/262144 : ℝ)) hmem 8 (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33797/262144 : ℝ))) hcmem 8 (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33797/262144 : ℝ)) (991990646511/1000000000000 : ℝ) (495995323257/500000000000 : ℝ) (251025009999/500000000000 : ℝ) (62756252501/125000000000 : ℝ) (397492824177/500000000000 : ℝ) (794985648373/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1364_exp_lower
  have heNumeric : (2054906239861/1000000000000 : ℝ)/4 ≤ Real.exp (-10657026233343/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906239861/1000000000000 : ℝ)/4 ≤ Real.exp ((8449/65536 : ℝ)-(794985648373/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8449/65536 : ℝ) (33797/262144 : ℝ) (794985648373/1000000000000 : ℝ) (2054906239861/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1365; no trusted numerical premise.
theorem cover8_leaf1365_exp_radius : (498993754997469197/500000000000000000 : ℝ) ≤ Real.exp ((-16899/1048576 : ℝ)/8) ∧ Real.exp ((-16899/1048576 : ℝ)/8) ≤ (199597501998987679/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16899/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1365_exp_lower : (460056857058449461/500000000000000000 : ℝ) ≤ Real.exp ((-42628103309419/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628103309419/64000000000000 : ℝ)/8) ≤ (920113714116898923/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628103309419/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1365_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906292003/1000000000000 : ℝ) ≤ 4*Real.exp (33797/262144 : ℝ)*Real.exp (-mu (radius 8 (16899/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906292003/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16899/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1365_exp_radius
  have hrNumeric : (246003256977/250000000000 : ℝ) ≤ Real.exp (-16899/1048576 : ℝ) ∧ Real.exp (-16899/1048576 : ℝ) ≤ (984013027909/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246003256977/250000000000 : ℝ) ≤ (radius 8 (16899/131072 : ℝ)) ∧ (radius 8 (16899/131072 : ℝ)) ≤ (984013027909/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16899/131072 : ℝ)) (246003256977/250000000000 : ℝ) (984013027909/1000000000000 : ℝ) (89048246621/500000000000 : ℝ) (178096493249/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16899/131072 : ℝ)) (246003256977/250000000000 : ℝ) (984013027909/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16899/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246003256977/250000000000 : ℝ) (984013027909/1000000000000 : ℝ) (496003256977/500000000000 : ℝ) (198401302791/200000000000 : ℝ) (123996788511/125000000000 : ℝ) (99197430809/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16899/131072 : ℝ)) 1 (496003256977/500000000000 : ℝ) (198401302791/200000000000 : ℝ) (123996788511/125000000000 : ℝ) (99197430809/100000000000 : ℝ) (991990411021/1000000000000 : ℝ) (991990411023/1000000000000 : ℝ) (99199041089/100000000000 : ℝ) (247997602723/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16899/131072 : ℝ)) 2 (991990411021/1000000000000 : ℝ) (991990411023/1000000000000 : ℝ) (99199041089/100000000000 : ℝ) (247997602723/250000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16899/131072 : ℝ)) 3 (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16899/131072 : ℝ)) 4 (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16899/131072 : ℝ)) 5 (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16899/131072 : ℝ)) 6 (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16899/131072 : ℝ)) 7 (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16899/131072 : ℝ))) (89048246621/500000000000 : ℝ) (178096493249/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16899/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89048246621/500000000000 : ℝ) (178096493249/1000000000000 : ℝ) (589048246621/1000000000000 : ℝ) (4712385973/8000000000 : ℝ) (422014802159/1000000000000 : ℝ) (422014802169/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16899/131072 : ℝ))) 1 (589048246621/1000000000000 : ℝ) (4712385973/8000000000 : ℝ) (422014802159/1000000000000 : ℝ) (422014802169/1000000000000 : ℝ) (50553152439/100000000000 : ℝ) (505531524397/1000000000000 : ℝ) (498585077253/1000000000000 : ℝ) (249292538631/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16899/131072 : ℝ))) 2 (50553152439/100000000000 : ℝ) (505531524397/1000000000000 : ℝ) (498585077253/1000000000000 : ℝ) (249292538631/500000000000 : ℝ) (502058300821/1000000000000 : ℝ) (50205830083/100000000000 : ℝ) (502046286851/1000000000000 : ℝ) (25102314343/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16899/131072 : ℝ))) 3 (502058300821/1000000000000 : ℝ) (50205830083/100000000000 : ℝ) (502046286851/1000000000000 : ℝ) (25102314343/50000000000 : ℝ) (125513073459/250000000000 : ℝ) (100410458769/200000000000 : ℝ) (2510261469/5000000000 : ℝ) (50205229381/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16899/131072 : ℝ))) 4 (125513073459/250000000000 : ℝ) (100410458769/200000000000 : ℝ) (2510261469/5000000000 : ℝ) (50205229381/100000000000 : ℝ) (251026146909/500000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16899/131072 : ℝ))) 5 (251026146909/500000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16899/131072 : ℝ))) 6 (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16899/131072 : ℝ))) 7 (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16899/131072 : ℝ)) hmem 8 (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16899/131072 : ℝ))) hcmem 8 (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16899/131072 : ℝ)) (198398082191/200000000000 : ℝ) (495995205479/500000000000 : ℝ) (502052293817/1000000000000 : ℝ) (125513073457/250000000000 : ℝ) (31799577507/40000000000 : ℝ) (3105427491/3906250000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1365_exp_lower
  have heNumeric : (2054906292003/1000000000000 : ℝ)/4 ≤ Real.exp (-42628103309419/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906292003/1000000000000 : ℝ)/4 ≤ Real.exp ((33797/262144 : ℝ)-(3105427491/3906250000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33797/262144 : ℝ) (16899/131072 : ℝ) (3105427491/3906250000 : ℝ) (2054906292003/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1366; no trusted numerical premise.
theorem cover8_leaf1366_exp_radius : (997987450510249143/1000000000000000000 : ℝ) ≤ Real.exp ((-33799/2097152 : ℝ)/8) ∧ Real.exp ((-33799/2097152 : ℝ)/8) ≤ (124748431313781143/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33799/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1366_exp_lower : (184022743408831249/200000000000000000 : ℝ) ≤ Real.exp ((-21314050840269/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314050840269/32000000000000 : ℝ)/8) ≤ (460056858522078123/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314050840269/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1366_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906344303/1000000000000 : ℝ) ≤ 4*Real.exp (16899/131072 : ℝ)*Real.exp (-mu (radius 8 (33799/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906344303/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33799/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1366_exp_radius
  have hrNumeric : (492006279347/500000000000 : ℝ) ≤ Real.exp (-33799/2097152 : ℝ) ∧ Real.exp (-33799/2097152 : ℝ) ≤ (196802511739/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492006279347/500000000000 : ℝ) ≤ (radius 8 (33799/262144 : ℝ)) ∧ (radius 8 (33799/262144 : ℝ)) ≤ (196802511739/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33799/262144 : ℝ)) (492006279347/500000000000 : ℝ) (196802511739/200000000000 : ℝ) (178099085709/1000000000000 : ℝ) (35619817143/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33799/262144 : ℝ)) (492006279347/500000000000 : ℝ) (196802511739/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33799/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492006279347/500000000000 : ℝ) (196802511739/200000000000 : ℝ) (992006279347/1000000000000 : ℝ) (248001569837/250000000000 : ℝ) (991974071583/1000000000000 : ℝ) (198394814317/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33799/262144 : ℝ)) 1 (992006279347/1000000000000 : ℝ) (248001569837/250000000000 : ℝ) (991974071583/1000000000000 : ℝ) (198394814317/200000000000 : ℝ) (198398035093/200000000000 : ℝ) (991990175467/1000000000000 : ℝ) (495995087667/500000000000 : ℝ) (123998771917/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33799/262144 : ℝ)) 2 (198398035093/200000000000 : ℝ) (991990175467/1000000000000 : ℝ) (495995087667/500000000000 : ℝ) (123998771917/125000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33799/262144 : ℝ)) 3 (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33799/262144 : ℝ)) 4 (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33799/262144 : ℝ)) 5 (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33799/262144 : ℝ)) 6 (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33799/262144 : ℝ)) 7 (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33799/262144 : ℝ))) (178099085709/1000000000000 : ℝ) (35619817143/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33799/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178099085709/1000000000000 : ℝ) (35619817143/200000000000 : ℝ) (294524771427/500000000000 : ℝ) (294524771429/500000000000 : ℝ) (105504468421/250000000000 : ℝ) (105504468423/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33799/262144 : ℝ))) 1 (294524771427/500000000000 : ℝ) (294524771429/500000000000 : ℝ) (105504468421/250000000000 : ℝ) (105504468423/250000000000 : ℝ) (505533708269/1000000000000 : ℝ) (20221348331/40000000000 : ℝ) (124646860061/250000000000 : ℝ) (124646860063/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33799/262144 : ℝ))) 2 (505533708269/1000000000000 : ℝ) (20221348331/40000000000 : ℝ) (124646860061/250000000000 : ℝ) (124646860063/250000000000 : ℝ) (31378785891/62500000000 : ℝ) (62757571783/125000000000 : ℝ) (1568901753/3125000000 : ℝ) (62756070121/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33799/262144 : ℝ))) 3 (31378785891/62500000000 : ℝ) (62757571783/125000000000 : ℝ) (1568901753/3125000000 : ℝ) (62756070121/125000000000 : ℝ) (62756820951/125000000000 : ℝ) (7844602619/15625000000 : ℝ) (125513641893/250000000000 : ℝ) (502054567581/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33799/262144 : ℝ))) 4 (62756820951/125000000000 : ℝ) (7844602619/15625000000 : ℝ) (125513641893/250000000000 : ℝ) (502054567581/1000000000000 : ℝ) (50205456759/100000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33799/262144 : ℝ))) 5 (50205456759/100000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33799/262144 : ℝ))) 6 (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33799/262144 : ℝ))) 7 (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33799/262144 : ℝ)) hmem 8 (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33799/262144 : ℝ))) hcmem 8 (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33799/262144 : ℝ)) (991990175399/1000000000000 : ℝ) (495995087701/500000000000 : ℝ) (502054567589/1000000000000 : ℝ) (502054567599/1000000000000 : ℝ) (794993226923/1000000000000 : ℝ) (397496613471/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1366_exp_lower
  have heNumeric : (2054906344303/1000000000000 : ℝ)/4 ≤ Real.exp (-21314050840269/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906344303/1000000000000 : ℝ)/4 ≤ Real.exp ((16899/131072 : ℝ)-(397496613471/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16899/131072 : ℝ) (33799/262144 : ℝ) (397496613471/500000000000 : ℝ) (2054906344303/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1367; no trusted numerical premise.
theorem cover8_leaf1367_exp_radius : (498993695512781719/500000000000000000 : ℝ) ≤ Real.exp ((-4225/262144 : ℝ)/8) ∧ Real.exp ((-4225/262144 : ℝ)/8) ≤ (997987391025563439/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4225/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1367_exp_lower : (9201137199804997/10000000000000000 : ℝ) ≤ Real.exp ((-42628100046601/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628100046601/64000000000000 : ℝ)/8) ≤ (920113719980499701/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628100046601/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1367_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981279353/200000000000 : ℝ) ≤ 4*Real.exp (33799/262144 : ℝ)*Real.exp (-mu (radius 8 (4225/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (410981279353/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4225/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1367_exp_radius
  have hrNumeric : (984012089481/1000000000000 : ℝ) ≤ Real.exp (-4225/262144 : ℝ) ∧ Real.exp (-4225/262144 : ℝ) ≤ (492006044741/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984012089481/1000000000000 : ℝ) ≤ (radius 8 (4225/32768 : ℝ)) ∧ (radius 8 (4225/32768 : ℝ)) ≤ (492006044741/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4225/32768 : ℝ)) (984012089481/1000000000000 : ℝ) (492006044741/500000000000 : ℝ) (178101678131/1000000000000 : ℝ) (89050839069/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4225/32768 : ℝ)) (984012089481/1000000000000 : ℝ) (492006044741/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4225/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984012089481/1000000000000 : ℝ) (492006044741/500000000000 : ℝ) (49600302237/50000000000 : ℝ) (992006044741/1000000000000 : ℝ) (495986917539/500000000000 : ℝ) (24799345877/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4225/32768 : ℝ)) 1 (49600302237/50000000000 : ℝ) (992006044741/1000000000000 : ℝ) (495986917539/500000000000 : ℝ) (24799345877/25000000000 : ℝ) (991989939909/1000000000000 : ℝ) (991989939911/1000000000000 : ℝ) (495994969889/500000000000 : ℝ) (49599496989/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4225/32768 : ℝ)) 2 (991989939909/1000000000000 : ℝ) (991989939911/1000000000000 : ℝ) (495994969889/500000000000 : ℝ) (49599496989/50000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4225/32768 : ℝ)) 3 (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4225/32768 : ℝ)) 4 (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4225/32768 : ℝ)) 5 (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4225/32768 : ℝ)) 6 (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4225/32768 : ℝ)) 7 (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4225/32768 : ℝ))) (178101678131/1000000000000 : ℝ) (89050839069/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4225/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178101678131/1000000000000 : ℝ) (89050839069/500000000000 : ℝ) (117810167813/200000000000 : ℝ) (589050839069/1000000000000 : ℝ) (422020945133/1000000000000 : ℝ) (211010472571/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4225/32768 : ℝ))) 1 (117810167813/200000000000 : ℝ) (589050839069/1000000000000 : ℝ) (422020945133/1000000000000 : ℝ) (211010472571/500000000000 : ℝ) (505535892099/1000000000000 : ℝ) (252767946053/500000000000 : ℝ) (249294901589/500000000000 : ℝ) (249294901593/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4225/32768 : ℝ))) 2 (505535892099/1000000000000 : ℝ) (252767946053/500000000000 : ℝ) (249294901589/500000000000 : ℝ) (249294901593/500000000000 : ℝ) (251031423819/500000000000 : ℝ) (251031423823/500000000000 : ℝ) (62756354377/125000000000 : ℝ) (20082033401/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4225/32768 : ℝ))) 3 (251031423819/500000000000 : ℝ) (251031423823/500000000000 : ℝ) (62756354377/125000000000 : ℝ) (20082033401/40000000000 : ℝ) (502056841327/1000000000000 : ℝ) (62757105167/125000000000 : ℝ) (502056841291/1000000000000 : ℝ) (5020568413/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4225/32768 : ℝ))) 4 (502056841327/1000000000000 : ℝ) (62757105167/125000000000 : ℝ) (502056841291/1000000000000 : ℝ) (5020568413/10000000000 : ℝ) (502056841309/1000000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4225/32768 : ℝ))) 5 (502056841309/1000000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4225/32768 : ℝ))) 6 (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4225/32768 : ℝ))) 7 (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4225/32768 : ℝ)) hmem 8 (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4225/32768 : ℝ))) hcmem 8 (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4225/32768 : ℝ)) (991989939843/1000000000000 : ℝ) (495994969923/500000000000 : ℝ) (125514210327/250000000000 : ℝ) (251028420659/500000000000 : ℝ) (794997016089/1000000000000 : ℝ) (794997016109/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1367_exp_lower
  have heNumeric : (410981279353/200000000000 : ℝ)/4 ≤ Real.exp (-42628100046601/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981279353/200000000000 : ℝ)/4 ≤ Real.exp ((33799/262144 : ℝ)-(794997016109/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33799/262144 : ℝ) (4225/32768 : ℝ) (794997016109/1000000000000 : ℝ) (410981279353/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1368; no trusted numerical premise.
theorem cover8_leaf1368_exp_radius : (498993665770440639/500000000000000000 : ℝ) ≤ Real.exp ((-33801/2097152 : ℝ)/8) ∧ Real.exp ((-33801/2097152 : ℝ)/8) ≤ (997987331540881279/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33801/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1368_exp_lower : (184022744584955829/200000000000000000 : ℝ) ≤ Real.exp ((-5328512301031/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328512301031/8000000000000 : ℝ)/8) ≤ (460056861462389573/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328512301031/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1368_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054906449369/1000000000000 : ℝ) ≤ 4*Real.exp (4225/32768 : ℝ)*Real.exp (-mu (radius 8 (33801/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054906449369/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33801/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1368_exp_radius
  have hrNumeric : (984011620267/1000000000000 : ℝ) ≤ Real.exp (-33801/2097152 : ℝ) ∧ Real.exp (-33801/2097152 : ℝ) ≤ (246002905067/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984011620267/1000000000000 : ℝ) ≤ (radius 8 (33801/262144 : ℝ)) ∧ (radius 8 (33801/262144 : ℝ)) ≤ (246002905067/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33801/262144 : ℝ)) (984011620267/1000000000000 : ℝ) (246002905067/250000000000 : ℝ) (4452606763/25000000000 : ℝ) (89052135263/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33801/262144 : ℝ)) (984011620267/1000000000000 : ℝ) (246002905067/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33801/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984011620267/1000000000000 : ℝ) (246002905067/250000000000 : ℝ) (992005810133/1000000000000 : ℝ) (496002905067/500000000000 : ℝ) (991973598573/1000000000000 : ℝ) (39678943943/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33801/262144 : ℝ)) 1 (992005810133/1000000000000 : ℝ) (496002905067/500000000000 : ℝ) (991973598573/1000000000000 : ℝ) (39678943943/40000000000 : ℝ) (991989704353/1000000000000 : ℝ) (198397940871/200000000000 : ℝ) (495994852111/500000000000 : ℝ) (30999678257/31250000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33801/262144 : ℝ)) 2 (991989704353/1000000000000 : ℝ) (198397940871/200000000000 : ℝ) (495994852111/500000000000 : ℝ) (30999678257/31250000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33801/262144 : ℝ)) 3 (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33801/262144 : ℝ)) 4 (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33801/262144 : ℝ)) 5 (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33801/262144 : ℝ)) 6 (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33801/262144 : ℝ)) 7 (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33801/262144 : ℝ))) (4452606763/25000000000 : ℝ) (89052135263/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33801/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4452606763/25000000000 : ℝ) (89052135263/500000000000 : ℝ) (29452606763/50000000000 : ℝ) (589052135263/1000000000000 : ℝ) (10550600413/25000000000 : ℝ) (26376501033/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33801/262144 : ℝ))) 1 (29452606763/50000000000 : ℝ) (589052135263/1000000000000 : ℝ) (10550600413/25000000000 : ℝ) (26376501033/62500000000 : ℝ) (50553807589/100000000000 : ℝ) (63192259487/125000000000 : ℝ) (99718433213/200000000000 : ℝ) (62324020759/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33801/262144 : ℝ))) 2 (50553807589/100000000000 : ℝ) (63192259487/125000000000 : ℝ) (99718433213/200000000000 : ℝ) (62324020759/125000000000 : ℝ) (502065120977/1000000000000 : ℝ) (62758140123/125000000000 : ℝ) (502053109029/1000000000000 : ℝ) (502053109037/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33801/262144 : ℝ))) 3 (502065120977/1000000000000 : ℝ) (62758140123/125000000000 : ℝ) (502053109029/1000000000000 : ℝ) (502053109037/1000000000000 : ℝ) (502059115003/1000000000000 : ℝ) (502059115011/1000000000000 : ℝ) (502059114967/1000000000000 : ℝ) (20082364599/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33801/262144 : ℝ))) 4 (502059115003/1000000000000 : ℝ) (502059115011/1000000000000 : ℝ) (502059114967/1000000000000 : ℝ) (20082364599/40000000000 : ℝ) (100411822997/200000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33801/262144 : ℝ))) 5 (100411822997/200000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33801/262144 : ℝ))) 6 (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33801/262144 : ℝ))) 7 (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33801/262144 : ℝ)) hmem 8 (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33801/262144 : ℝ))) hcmem 8 (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33801/262144 : ℝ)) (991989704287/1000000000000 : ℝ) (99198970429/100000000000 : ℝ) (62757389373/125000000000 : ℝ) (502059114993/1000000000000 : ℝ) (79500080519/100000000000 : ℝ) (795000805207/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1368_exp_lower
  have heNumeric : (2054906449369/1000000000000 : ℝ)/4 ≤ Real.exp (-5328512301031/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054906449369/1000000000000 : ℝ)/4 ≤ Real.exp ((4225/32768 : ℝ)-(795000805207/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4225/32768 : ℝ) (33801/262144 : ℝ) (795000805207/1000000000000 : ℝ) (2054906449369/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1369; no trusted numerical premise.
theorem cover8_leaf1369_exp_radius : (124748409007025333/125000000000000000 : ℝ) ≤ Real.exp ((-16901/1048576 : ℝ)/8) ∧ Real.exp ((-16901/1048576 : ℝ)/8) ≤ (199597454411240533/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16901/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1369_exp_lower : (115014215734782467/125000000000000000 : ℝ) ≤ Real.exp ((-1705123870591/2560000000000 : ℝ)/8) ∧ Real.exp ((-1705123870591/2560000000000 : ℝ)/8) ≤ (920113725878259737/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1705123870591/2560000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1369_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453251069/500000000000 : ℝ) ≤ 4*Real.exp (33801/262144 : ℝ)*Real.exp (-mu (radius 8 (16901/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453251069/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16901/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1369_exp_radius
  have hrNumeric : (492005575527/500000000000 : ℝ) ≤ Real.exp (-16901/1048576 : ℝ) ∧ Real.exp (-16901/1048576 : ℝ) ≤ (196802230211/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492005575527/500000000000 : ℝ) ≤ (radius 8 (16901/131072 : ℝ)) ∧ (radius 8 (16901/131072 : ℝ)) ≤ (196802230211/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16901/131072 : ℝ)) (492005575527/500000000000 : ℝ) (196802230211/200000000000 : ℝ) (11131678929/62500000000 : ℝ) (17810686287/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16901/131072 : ℝ)) (492005575527/500000000000 : ℝ) (196802230211/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16901/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492005575527/500000000000 : ℝ) (196802230211/200000000000 : ℝ) (992005575527/1000000000000 : ℝ) (124000696941/125000000000 : ℝ) (247993340517/250000000000 : ℝ) (99197336207/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16901/131072 : ℝ)) 1 (992005575527/1000000000000 : ℝ) (124000696941/125000000000 : ℝ) (247993340517/250000000000 : ℝ) (99197336207/100000000000 : ℝ) (991989468797/1000000000000 : ℝ) (991989468799/1000000000000 : ℝ) (495994734333/500000000000 : ℝ) (991989468669/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16901/131072 : ℝ)) 2 (991989468797/1000000000000 : ℝ) (991989468799/1000000000000 : ℝ) (495994734333/500000000000 : ℝ) (991989468669/1000000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16901/131072 : ℝ)) 3 (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16901/131072 : ℝ)) 4 (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16901/131072 : ℝ)) 5 (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16901/131072 : ℝ)) 6 (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16901/131072 : ℝ)) 7 (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16901/131072 : ℝ))) (11131678929/62500000000 : ℝ) (17810686287/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16901/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11131678929/62500000000 : ℝ) (17810686287/100000000000 : ℝ) (73631678929/125000000000 : ℝ) (117810686287/200000000000 : ℝ) (52753385979/125000000000 : ℝ) (2637669299/6250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16901/131072 : ℝ))) 1 (73631678929/125000000000 : ℝ) (117810686287/200000000000 : ℝ) (52753385979/125000000000 : ℝ) (2637669299/6250000000 : ℝ) (31596266227/62500000000 : ℝ) (252770129819/500000000000 : ℝ) (99718905779/200000000000 : ℝ) (249297264451/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16901/131072 : ℝ))) 2 (31596266227/62500000000 : ℝ) (252770129819/500000000000 : ℝ) (99718905779/200000000000 : ℝ) (249297264451/500000000000 : ℝ) (502067394263/1000000000000 : ℝ) (50206739427/100000000000 : ℝ) (502055382989/1000000000000 : ℝ) (125513845749/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16901/131072 : ℝ))) 3 (502067394263/1000000000000 : ℝ) (50206739427/100000000000 : ℝ) (502055382989/1000000000000 : ℝ) (125513845749/250000000000 : ℝ) (251030694313/500000000000 : ℝ) (502061388633/1000000000000 : ℝ) (50206138859/100000000000 : ℝ) (251030694299/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16901/131072 : ℝ))) 4 (251030694313/500000000000 : ℝ) (502061388633/1000000000000 : ℝ) (50206138859/100000000000 : ℝ) (251030694299/500000000000 : ℝ) (7844709197/15625000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16901/131072 : ℝ))) 5 (7844709197/15625000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16901/131072 : ℝ))) 6 (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16901/131072 : ℝ))) 7 (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16901/131072 : ℝ)) hmem 8 (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16901/131072 : ℝ))) hcmem 8 (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16901/131072 : ℝ)) (991989468731/1000000000000 : ℝ) (495994734367/500000000000 : ℝ) (502061388607/1000000000000 : ℝ) (62757673577/125000000000 : ℝ) (795004594207/1000000000000 : ℝ) (31800183769/40000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1369_exp_lower
  have heNumeric : (1027453251069/500000000000 : ℝ)/4 ≤ Real.exp (-1705123870591/2560000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453251069/500000000000 : ℝ)/4 ≤ Real.exp ((33801/262144 : ℝ)-(31800183769/40000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33801/262144 : ℝ) (16901/131072 : ℝ) (31800183769/40000000000 : ℝ) (1027453251069/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1370; no trusted numerical premise.
theorem cover8_leaf1370_exp_radius : (249496803142881899/250000000000000000 : ℝ) ≤ Real.exp ((-33803/2097152 : ℝ)/8) ∧ Real.exp ((-33803/2097152 : ℝ)/8) ≤ (997987212571527597/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33803/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1370_exp_lower : (7360909830721091/8000000000000000 : ℝ) ≤ Real.exp ((-4262809511663/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262809511663/6400000000000 : ℝ)/8) ≤ (115014216105017047/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262809511663/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1370_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431659691/62500000000 : ℝ) ≤ 4*Real.exp (16901/131072 : ℝ)*Real.exp (-mu (radius 8 (33803/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (128431659691/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33803/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1370_exp_radius
  have hrNumeric : (984010681841/1000000000000 : ℝ) ≤ Real.exp (-33803/2097152 : ℝ) ∧ Real.exp (-33803/2097152 : ℝ) ≤ (492005340921/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984010681841/1000000000000 : ℝ) ≤ (radius 8 (33803/262144 : ℝ)) ∧ (radius 8 (33803/262144 : ℝ)) ≤ (492005340921/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33803/262144 : ℝ)) (984010681841/1000000000000 : ℝ) (492005340921/500000000000 : ℝ) (178109455169/1000000000000 : ℝ) (22263681897/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33803/262144 : ℝ)) (984010681841/1000000000000 : ℝ) (492005340921/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33803/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984010681841/1000000000000 : ℝ) (492005340921/500000000000 : ℝ) (24800133523/25000000000 : ℝ) (992005340921/1000000000000 : ℝ) (991973125563/1000000000000 : ℝ) (198394625113/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33803/262144 : ℝ)) 1 (24800133523/25000000000 : ℝ) (992005340921/1000000000000 : ℝ) (991973125563/1000000000000 : ℝ) (198394625113/200000000000 : ℝ) (991989233241/1000000000000 : ℝ) (991989233243/1000000000000 : ℝ) (99198923311/100000000000 : ℝ) (991989233113/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33803/262144 : ℝ)) 2 (991989233241/1000000000000 : ℝ) (991989233243/1000000000000 : ℝ) (99198923311/100000000000 : ℝ) (991989233113/1000000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33803/262144 : ℝ)) 3 (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33803/262144 : ℝ)) 4 (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33803/262144 : ℝ)) 5 (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33803/262144 : ℝ)) 6 (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33803/262144 : ℝ)) 7 (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33803/262144 : ℝ))) (178109455169/1000000000000 : ℝ) (22263681897/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33803/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178109455169/1000000000000 : ℝ) (22263681897/125000000000 : ℝ) (18407960237/31250000000 : ℝ) (147263681897/250000000000 : ℝ) (16881206363/40000000000 : ℝ) (105507539771/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33803/262144 : ℝ))) 1 (18407960237/31250000000 : ℝ) (147263681897/250000000000 : ℝ) (16881206363/40000000000 : ℝ) (105507539771/250000000000 : ℝ) (505542443329/1000000000000 : ℝ) (63192805417/125000000000 : ℝ) (498596891673/1000000000000 : ℝ) (498596891681/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33803/262144 : ℝ))) 2 (505542443329/1000000000000 : ℝ) (63192805417/125000000000 : ℝ) (498596891673/1000000000000 : ℝ) (498596891681/1000000000000 : ℝ) (502069667501/1000000000000 : ℝ) (502069667509/1000000000000 : ℝ) (5020576569/10000000000 : ℝ) (502057656909/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33803/262144 : ℝ))) 3 (502069667501/1000000000000 : ℝ) (502069667509/1000000000000 : ℝ) (5020576569/10000000000 : ℝ) (502057656909/1000000000000 : ℝ) (2510318311/5000000000 : ℝ) (502063662209/1000000000000 : ℝ) (125515915541/250000000000 : ℝ) (251031831087/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33803/262144 : ℝ))) 4 (2510318311/5000000000 : ℝ) (502063662209/1000000000000 : ℝ) (125515915541/250000000000 : ℝ) (251031831087/500000000000 : ℝ) (251031831091/500000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33803/262144 : ℝ))) 5 (251031831091/500000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33803/262144 : ℝ))) 6 (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33803/262144 : ℝ))) 7 (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33803/262144 : ℝ)) hmem 8 (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33803/262144 : ℝ))) hcmem 8 (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33803/262144 : ℝ)) (39679569327/40000000000 : ℝ) (495994616589/500000000000 : ℝ) (502063662181/1000000000000 : ℝ) (31378978887/62500000000 : ℝ) (15900167663/20000000000 : ℝ) (79500838317/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1370_exp_lower
  have heNumeric : (128431659691/62500000000 : ℝ)/4 ≤ Real.exp (-4262809511663/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431659691/62500000000 : ℝ)/4 ≤ Real.exp ((16901/131072 : ℝ)-(79500838317/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16901/131072 : ℝ) (33803/262144 : ℝ) (79500838317/100000000000 : ℝ) (128431659691/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1371; no trusted numerical premise.
theorem cover8_leaf1371_exp_radius : (997987153086856073/1000000000000000000 : ℝ) ≤ Real.exp ((-8451/524288 : ℝ)/8) ∧ Real.exp ((-8451/524288 : ℝ)/8) ≤ (498993576543428037/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8451/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1371_exp_lower : (920113731810984133/1000000000000000000 : ℝ) ≤ Real.exp ((-42628093463493/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628093463493/64000000000000 : ℝ)/8) ≤ (460056865905492067/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628093463493/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1371_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410981321627/200000000000 : ℝ) ≤ 4*Real.exp (33803/262144 : ℝ)*Real.exp (-mu (radius 8 (8451/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (410981321627/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8451/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1371_exp_radius
  have hrNumeric : (246002553157/250000000000 : ℝ) ≤ Real.exp (-8451/524288 : ℝ) ∧ Real.exp (-8451/524288 : ℝ) ≤ (984010212629/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246002553157/250000000000 : ℝ) ≤ (radius 8 (8451/65536 : ℝ)) ∧ (radius 8 (8451/65536 : ℝ)) ≤ (984010212629/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8451/65536 : ℝ)) (246002553157/250000000000 : ℝ) (984010212629/1000000000000 : ℝ) (35622409487/200000000000 : ℝ) (89056023721/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8451/65536 : ℝ)) (246002553157/250000000000 : ℝ) (984010212629/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8451/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246002553157/250000000000 : ℝ) (984010212629/1000000000000 : ℝ) (496002553157/500000000000 : ℝ) (198401021263/200000000000 : ℝ) (495986444529/500000000000 : ℝ) (49598644453/50000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8451/65536 : ℝ)) 1 (496002553157/500000000000 : ℝ) (198401021263/200000000000 : ℝ) (495986444529/500000000000 : ℝ) (49598644453/50000000000 : ℝ) (495994498843/500000000000 : ℝ) (123998624711/125000000000 : ℝ) (198397799511/200000000000 : ℝ) (991988997557/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8451/65536 : ℝ)) 2 (495994498843/500000000000 : ℝ) (123998624711/125000000000 : ℝ) (198397799511/200000000000 : ℝ) (991988997557/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8451/65536 : ℝ)) 3 (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8451/65536 : ℝ)) 4 (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8451/65536 : ℝ)) 5 (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8451/65536 : ℝ)) 6 (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8451/65536 : ℝ)) 7 (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8451/65536 : ℝ))) (35622409487/200000000000 : ℝ) (89056023721/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8451/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35622409487/200000000000 : ℝ) (89056023721/500000000000 : ℝ) (589056023717/1000000000000 : ℝ) (589056023721/1000000000000 : ℝ) (422033230249/1000000000000 : ℝ) (211016615129/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8451/65536 : ℝ))) 1 (589056023717/1000000000000 : ℝ) (589056023721/1000000000000 : ℝ) (422033230249/1000000000000 : ℝ) (211016615129/500000000000 : ℝ) (505544626983/1000000000000 : ℝ) (50554462699/100000000000 : ℝ) (249299627199/500000000000 : ℝ) (249299627203/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8451/65536 : ℝ))) 2 (505544626983/1000000000000 : ℝ) (50554462699/100000000000 : ℝ) (249299627199/500000000000 : ℝ) (249299627203/500000000000 : ℝ) (50207194069/100000000000 : ℝ) (251035970349/500000000000 : ℝ) (502059930763/1000000000000 : ℝ) (125514982693/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8451/65536 : ℝ))) 3 (50207194069/100000000000 : ℝ) (251035970349/500000000000 : ℝ) (502059930763/1000000000000 : ℝ) (125514982693/250000000000 : ℝ) (251032967863/500000000000 : ℝ) (100413187147/200000000000 : ℝ) (50206593569/100000000000 : ℝ) (5020659357/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8451/65536 : ℝ))) 4 (251032967863/500000000000 : ℝ) (100413187147/200000000000 : ℝ) (50206593569/100000000000 : ℝ) (5020659357/10000000000 : ℝ) (125516483927/250000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8451/65536 : ℝ))) 5 (125516483927/250000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8451/65536 : ℝ))) 6 (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8451/65536 : ℝ))) 7 (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8451/65536 : ℝ)) hmem 8 (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8451/65536 : ℝ))) hcmem 8 (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8451/65536 : ℝ)) (49599449881/50000000000 : ℝ) (991988997623/1000000000000 : ℝ) (502065935707/1000000000000 : ℝ) (251032967859/500000000000 : ℝ) (795012172017/1000000000000 : ℝ) (795012172037/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1371_exp_lower
  have heNumeric : (410981321627/200000000000 : ℝ)/4 ≤ Real.exp (-42628093463493/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410981321627/200000000000 : ℝ)/4 ≤ Real.exp ((33803/262144 : ℝ)-(795012172037/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33803/262144 : ℝ) (8451/65536 : ℝ) (795012172037/1000000000000 : ℝ) (410981321627/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1372; no trusted numerical premise.
theorem cover8_leaf1372_exp_radius : (199597418720437619/200000000000000000 : ℝ) ≤ Real.exp ((-33805/2097152 : ℝ)/8) ∧ Real.exp ((-33805/2097152 : ℝ)/8) ≤ (15593548337534189/15625000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33805/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1372_exp_lower : (920113734790803009/1000000000000000000 : ℝ) ≤ Real.exp ((-10657022951341/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657022951341/16000000000000 : ℝ)/8) ≤ (92011373479080301/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657022951341/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1372_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453330687/500000000000 : ℝ) ≤ 4*Real.exp (8451/65536 : ℝ)*Real.exp (-mu (radius 8 (33805/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453330687/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33805/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1372_exp_radius
  have hrNumeric : (123001217927/125000000000 : ℝ) ≤ Real.exp (-33805/2097152 : ℝ) ∧ Real.exp (-33805/2097152 : ℝ) ≤ (984009743417/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (123001217927/125000000000 : ℝ) ≤ (radius 8 (33805/262144 : ℝ)) ∧ (radius 8 (33805/262144 : ℝ)) ≤ (984009743417/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33805/262144 : ℝ)) (123001217927/125000000000 : ℝ) (984009743417/1000000000000 : ℝ) (178114639657/1000000000000 : ℝ) (11132164979/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33805/262144 : ℝ)) (123001217927/125000000000 : ℝ) (984009743417/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33805/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (123001217927/125000000000 : ℝ) (984009743417/1000000000000 : ℝ) (248001217927/250000000000 : ℝ) (992004871709/1000000000000 : ℝ) (495986326277/500000000000 : ℝ) (198394530511/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33805/262144 : ℝ)) 1 (248001217927/250000000000 : ℝ) (992004871709/1000000000000 : ℝ) (495986326277/500000000000 : ℝ) (198394530511/200000000000 : ℝ) (991988762131/1000000000000 : ℝ) (247997190533/250000000000 : ℝ) (495994381/500000000 : ℝ) (495994381001/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33805/262144 : ℝ)) 2 (991988762131/1000000000000 : ℝ) (247997190533/250000000000 : ℝ) (495994381/500000000 : ℝ) (495994381001/500000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33805/262144 : ℝ)) 3 (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33805/262144 : ℝ)) 4 (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33805/262144 : ℝ)) 5 (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33805/262144 : ℝ)) 6 (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33805/262144 : ℝ)) 7 (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33805/262144 : ℝ))) (178114639657/1000000000000 : ℝ) (11132164979/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33805/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178114639657/1000000000000 : ℝ) (11132164979/62500000000 : ℝ) (147264329957/250000000000 : ℝ) (73632164979/125000000000 : ℝ) (422036301349/1000000000000 : ℝ) (422036301359/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33805/262144 : ℝ))) 1 (147264329957/250000000000 : ℝ) (73632164979/125000000000 : ℝ) (422036301349/1000000000000 : ℝ) (422036301359/1000000000000 : ℝ) (126386702647/250000000000 : ℝ) (126386702649/250000000000 : ℝ) (498601617067/1000000000000 : ℝ) (124650404269/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33805/262144 : ℝ))) 2 (126386702647/250000000000 : ℝ) (126386702649/250000000000 : ℝ) (498601617067/1000000000000 : ℝ) (124650404269/250000000000 : ℝ) (502074213827/1000000000000 : ℝ) (125518553459/250000000000 : ℝ) (251031102287/500000000000 : ℝ) (62757775573/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33805/262144 : ℝ))) 3 (502074213827/1000000000000 : ℝ) (125518553459/250000000000 : ℝ) (251031102287/500000000000 : ℝ) (62757775573/125000000000 : ℝ) (1255170523/2500000000 : ℝ) (50206820921/100000000000 : ℝ) (125517052291/250000000000 : ℝ) (20082728367/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33805/262144 : ℝ))) 4 (1255170523/2500000000 : ℝ) (50206820921/100000000000 : ℝ) (125517052291/250000000000 : ℝ) (20082728367/40000000000 : ℝ) (251034104591/500000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33805/262144 : ℝ))) 5 (251034104591/500000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33805/262144 : ℝ))) 6 (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33805/262144 : ℝ))) 7 (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33805/262144 : ℝ)) hmem 8 (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33805/262144 : ℝ))) hcmem 8 (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33805/262144 : ℝ)) (198397752413/200000000000 : ℝ) (991988762067/1000000000000 : ℝ) (502068209181/1000000000000 : ℝ) (502068209193/1000000000000 : ℝ) (198753990201/250000000000 : ℝ) (397507980413/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1372_exp_lower
  have heNumeric : (1027453330687/500000000000 : ℝ)/4 ≤ Real.exp (-10657022951341/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453330687/500000000000 : ℝ)/4 ≤ Real.exp ((8451/65536 : ℝ)-(397507980413/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8451/65536 : ℝ) (33805/262144 : ℝ) (397507980413/500000000000 : ℝ) (1027453330687/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1373; no trusted numerical premise.
theorem cover8_leaf1373_exp_radius : (62374189632345229/62500000000000000 : ℝ) ≤ Real.exp ((-16903/1048576 : ℝ)/8) ∧ Real.exp ((-16903/1048576 : ℝ)/8) ≤ (199597406823504733/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16903/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1373_exp_lower : (920113737779593003/1000000000000000000 : ℝ) ≤ Real.exp ((-42628090142243/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628090142243/64000000000000 : ℝ)/8) ≤ (230028434444898251/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628090142243/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1373_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027453357387/500000000000 : ℝ) ≤ 4*Real.exp (33805/262144 : ℝ)*Real.exp (-mu (radius 8 (16903/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027453357387/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16903/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1373_exp_radius
  have hrNumeric : (246002318551/250000000000 : ℝ) ≤ Real.exp (-16903/1048576 : ℝ) ∧ Real.exp (-16903/1048576 : ℝ) ≤ (196801854841/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246002318551/250000000000 : ℝ) ≤ (radius 8 (16903/131072 : ℝ)) ∧ (radius 8 (16903/131072 : ℝ)) ≤ (196801854841/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16903/131072 : ℝ)) (246002318551/250000000000 : ℝ) (196801854841/200000000000 : ℝ) (1113232699/6250000000 : ℝ) (178117231847/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16903/131072 : ℝ)) (246002318551/250000000000 : ℝ) (196801854841/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16903/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246002318551/250000000000 : ℝ) (196801854841/200000000000 : ℝ) (496002318551/500000000000 : ℝ) (992004637103/1000000000000 : ℝ) (991972416049/1000000000000 : ℝ) (991972416051/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16903/131072 : ℝ)) 1 (496002318551/500000000000 : ℝ) (992004637103/1000000000000 : ℝ) (991972416049/1000000000000 : ℝ) (991972416051/1000000000000 : ℝ) (39679541063/40000000000 : ℝ) (991988526577/1000000000000 : ℝ) (247997131611/250000000000 : ℝ) (991988526447/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16903/131072 : ℝ)) 2 (39679541063/40000000000 : ℝ) (991988526577/1000000000000 : ℝ) (247997131611/250000000000 : ℝ) (991988526447/1000000000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16903/131072 : ℝ)) 3 (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16903/131072 : ℝ)) 4 (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16903/131072 : ℝ)) 5 (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16903/131072 : ℝ)) 6 (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16903/131072 : ℝ)) 7 (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16903/131072 : ℝ))) (1113232699/6250000000 : ℝ) (178117231847/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16903/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (1113232699/6250000000 : ℝ) (178117231847/1000000000000 : ℝ) (7363232699/12500000000 : ℝ) (147264653981/250000000000 : ℝ) (422039372381/1000000000000 : ℝ) (42203937239/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16903/131072 : ℝ))) 1 (7363232699/12500000000 : ℝ) (147264653981/250000000000 : ℝ) (422039372381/1000000000000 : ℝ) (42203937239/100000000000 : ℝ) (10110979883/20000000000 : ℝ) (505548994157/1000000000000 : ℝ) (99720795937/200000000000 : ℝ) (498603979693/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16903/131072 : ℝ))) 2 (10110979883/20000000000 : ℝ) (505548994157/1000000000000 : ℝ) (99720795937/200000000000 : ℝ) (498603979693/1000000000000 : ℝ) (502076486917/1000000000000 : ℝ) (20083059477/40000000000 : ℝ) (251032239169/500000000000 : ℝ) (251032239173/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16903/131072 : ℝ))) 3 (502076486917/1000000000000 : ℝ) (20083059477/40000000000 : ℝ) (251032239169/500000000000 : ℝ) (251032239173/500000000000 : ℝ) (502070482627/1000000000000 : ℝ) (125517620659/250000000000 : ℝ) (502070482591/1000000000000 : ℝ) (2510352413/5000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16903/131072 : ℝ))) 4 (502070482627/1000000000000 : ℝ) (125517620659/250000000000 : ℝ) (502070482591/1000000000000 : ℝ) (2510352413/5000000000 : ℝ) (502070482609/1000000000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16903/131072 : ℝ))) 5 (502070482609/1000000000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16903/131072 : ℝ))) 6 (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16903/131072 : ℝ))) 7 (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16903/131072 : ℝ)) hmem 8 (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16903/131072 : ℝ))) hcmem 8 (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16903/131072 : ℝ)) (991988526509/1000000000000 : ℝ) (61999282907/62500000000 : ℝ) (31379405163/62500000000 : ℝ) (251035241309/500000000000 : ℝ) (397509874759/500000000000 : ℝ) (795019749537/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1373_exp_lower
  have heNumeric : (1027453357387/500000000000 : ℝ)/4 ≤ Real.exp (-42628090142243/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027453357387/500000000000 : ℝ)/4 ≤ Real.exp ((33805/262144 : ℝ)-(795019749537/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33805/262144 : ℝ) (16903/131072 : ℝ) (795019749537/1000000000000 : ℝ) (1027453357387/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1374; no trusted numerical premise.
theorem cover8_leaf1374_exp_radius : (997986974632862777/1000000000000000000 : ℝ) ≤ Real.exp ((-33807/2097152 : ℝ)/8) ∧ Real.exp ((-33807/2097152 : ℝ)/8) ≤ (498993487316431389/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33807/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1374_exp_lower : (460056870387871959/500000000000000000 : ℝ) ≤ Real.exp ((-21314044237513/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314044237513/32000000000000 : ℝ)/8) ≤ (920113740775743919/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314044237513/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1374_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431673019/62500000000 : ℝ) ≤ 4*Real.exp (16903/131072 : ℝ)*Real.exp (-mu (radius 8 (33807/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (128431673019/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33807/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1374_exp_radius
  have hrNumeric : (984008804991/1000000000000 : ℝ) ≤ Real.exp (-33807/2097152 : ℝ) ∧ Real.exp (-33807/2097152 : ℝ) ≤ (7687568789/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984008804991/1000000000000 : ℝ) ≤ (radius 8 (33807/262144 : ℝ)) ∧ (radius 8 (33807/262144 : ℝ)) ≤ (7687568789/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33807/262144 : ℝ)) (984008804991/1000000000000 : ℝ) (7687568789/7812500000 : ℝ) (178119823989/1000000000000 : ℝ) (44529955999/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33807/262144 : ℝ)) (984008804991/1000000000000 : ℝ) (7687568789/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33807/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984008804991/1000000000000 : ℝ) (7687568789/7812500000 : ℝ) (198400880499/200000000000 : ℝ) (15500068789/15625000000 : ℝ) (123996522443/125000000000 : ℝ) (495986089773/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33807/262144 : ℝ)) 1 (198400880499/200000000000 : ℝ) (15500068789/15625000000 : ℝ) (123996522443/125000000000 : ℝ) (495986089773/500000000000 : ℝ) (991988291019/1000000000000 : ℝ) (991988291021/1000000000000 : ℝ) (123998536361/125000000000 : ℝ) (991988290891/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33807/262144 : ℝ)) 2 (991988291019/1000000000000 : ℝ) (991988291021/1000000000000 : ℝ) (123998536361/125000000000 : ℝ) (991988290891/1000000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33807/262144 : ℝ)) 3 (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33807/262144 : ℝ)) 4 (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33807/262144 : ℝ)) 5 (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33807/262144 : ℝ)) 6 (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33807/262144 : ℝ)) 7 (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33807/262144 : ℝ))) (178119823989/1000000000000 : ℝ) (44529955999/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33807/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178119823989/1000000000000 : ℝ) (44529955999/250000000000 : ℝ) (294529955997/500000000000 : ℝ) (294529955999/500000000000 : ℝ) (8440848867/20000000000 : ℝ) (422042443359/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33807/262144 : ℝ))) 1 (294529955997/500000000000 : ℝ) (294529955999/500000000000 : ℝ) (8440848867/20000000000 : ℝ) (422042443359/1000000000000 : ℝ) (63193897209/125000000000 : ℝ) (505551177679/1000000000000 : ℝ) (99721268451/200000000000 : ℝ) (498606342263/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33807/262144 : ℝ))) 2 (63193897209/125000000000 : ℝ) (505551177679/1000000000000 : ℝ) (99721268451/200000000000 : ℝ) (498606342263/1000000000000 : ℝ) (502078759963/1000000000000 : ℝ) (502078759971/1000000000000 : ℝ) (502066752057/1000000000000 : ℝ) (251033376033/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33807/262144 : ℝ))) 3 (502078759963/1000000000000 : ℝ) (502078759971/1000000000000 : ℝ) (502066752057/1000000000000 : ℝ) (251033376033/500000000000 : ℝ) (50207275601/100000000000 : ℝ) (502072756019/1000000000000 : ℝ) (251036377987/500000000000 : ℝ) (502072755983/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33807/262144 : ℝ))) 4 (50207275601/100000000000 : ℝ) (502072756019/1000000000000 : ℝ) (251036377987/500000000000 : ℝ) (502072755983/1000000000000 : ℝ) (62759094499/125000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33807/262144 : ℝ))) 5 (62759094499/125000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33807/262144 : ℝ))) 6 (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33807/262144 : ℝ))) 7 (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33807/262144 : ℝ)) hmem 8 (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33807/262144 : ℝ))) hcmem 8 (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33807/262144 : ℝ)) (991988290953/1000000000000 : ℝ) (247997072739/250000000000 : ℝ) (502072755991/1000000000000 : ℝ) (502072756001/1000000000000 : ℝ) (159004707633/200000000000 : ℝ) (99377942273/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1374_exp_lower
  have heNumeric : (128431673019/62500000000 : ℝ)/4 ≤ Real.exp (-21314044237513/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431673019/62500000000 : ℝ)/4 ≤ Real.exp ((16903/131072 : ℝ)-(99377942273/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16903/131072 : ℝ) (33807/262144 : ℝ) (99377942273/125000000000 : ℝ) (128431673019/62500000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1350_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1350_certificate
#check SmaleRate.Proofs.cover8_leaf1351_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1351_certificate
#check SmaleRate.Proofs.cover8_leaf1352_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1352_certificate
#check SmaleRate.Proofs.cover8_leaf1353_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1353_certificate
#check SmaleRate.Proofs.cover8_leaf1354_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1354_certificate
#check SmaleRate.Proofs.cover8_leaf1355_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1355_certificate
#check SmaleRate.Proofs.cover8_leaf1356_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1356_certificate
#check SmaleRate.Proofs.cover8_leaf1357_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1357_certificate
#check SmaleRate.Proofs.cover8_leaf1358_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1358_certificate
#check SmaleRate.Proofs.cover8_leaf1359_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1359_certificate
#check SmaleRate.Proofs.cover8_leaf1360_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1360_certificate
#check SmaleRate.Proofs.cover8_leaf1361_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1361_certificate
#check SmaleRate.Proofs.cover8_leaf1362_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1362_certificate
#check SmaleRate.Proofs.cover8_leaf1363_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1363_certificate
#check SmaleRate.Proofs.cover8_leaf1364_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1364_certificate
#check SmaleRate.Proofs.cover8_leaf1365_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1365_certificate
#check SmaleRate.Proofs.cover8_leaf1366_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1366_certificate
#check SmaleRate.Proofs.cover8_leaf1367_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1367_certificate
#check SmaleRate.Proofs.cover8_leaf1368_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1368_certificate
#check SmaleRate.Proofs.cover8_leaf1369_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1369_certificate
#check SmaleRate.Proofs.cover8_leaf1370_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1370_certificate
#check SmaleRate.Proofs.cover8_leaf1371_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1371_certificate
#check SmaleRate.Proofs.cover8_leaf1372_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1372_certificate
#check SmaleRate.Proofs.cover8_leaf1373_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1373_certificate
#check SmaleRate.Proofs.cover8_leaf1374_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1374_certificate
