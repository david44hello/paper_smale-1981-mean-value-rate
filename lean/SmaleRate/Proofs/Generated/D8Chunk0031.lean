/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
import SmaleRate.Proofs.AGMCertificates

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf0775; no trusted numerical premise.
theorem cover8_leaf0775_exp_radius : (998009757517352681/1000000000000000000 : ℝ) ≤ Real.exp ((-2089/131072 : ℝ)/8) ∧ Real.exp ((-2089/131072 : ℝ)/8) ≤ (499004878758676341/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2089/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0775_exp_lower : (115014181956481317/125000000000000000 : ℝ) ≤ Real.exp ((-85256494266161/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256494266161/128000000000000 : ℝ)/8) ≤ (920113455651850537/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256494266161/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0775_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901674131/1000000000000 : ℝ) ≤ 4*Real.exp (66847/524288 : ℝ)*Real.exp (-mu (radius 8 (2089/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901674131/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2089/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0775_exp_radius
  have hrNumeric : (61511783099/62500000000 : ℝ) ≤ Real.exp (-2089/131072 : ℝ) ∧ Real.exp (-2089/131072 : ℝ) ≤ (196837705917/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61511783099/62500000000 : ℝ) ≤ (radius 8 (2089/16384 : ℝ)) ∧ (radius 8 (2089/16384 : ℝ)) ≤ (196837705917/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2089/16384 : ℝ)) (61511783099/62500000000 : ℝ) (196837705917/200000000000 : ℝ) (88562037907/500000000000 : ℝ) (177124075821/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2089/16384 : ℝ)) (61511783099/62500000000 : ℝ) (196837705917/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2089/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61511783099/62500000000 : ℝ) (196837705917/200000000000 : ℝ) (124011783099/125000000000 : ℝ) (992094264793/1000000000000 : ℝ) (992062764941/1000000000000 : ℝ) (992062764943/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2089/16384 : ℝ)) 1 (124011783099/125000000000 : ℝ) (992094264793/1000000000000 : ℝ) (992062764941/1000000000000 : ℝ) (992062764943/1000000000000 : ℝ) (496039257433/500000000000 : ℝ) (248019628717/250000000000 : ℝ) (992078514741/1000000000000 : ℝ) (992078514743/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2089/16384 : ℝ)) 2 (496039257433/500000000000 : ℝ) (248019628717/250000000000 : ℝ) (992078514741/1000000000000 : ℝ) (992078514743/1000000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2089/16384 : ℝ)) 3 (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2089/16384 : ℝ)) 4 (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2089/16384 : ℝ)) 5 (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2089/16384 : ℝ)) 6 (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2089/16384 : ℝ)) 7 (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2089/16384 : ℝ))) (88562037907/500000000000 : ℝ) (177124075821/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2089/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88562037907/500000000000 : ℝ) (177124075821/1000000000000 : ℝ) (588562037907/1000000000000 : ℝ) (588562037911/1000000000000 : ℝ) (420861112261/1000000000000 : ℝ) (42086111227/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2089/16384 : ℝ))) 1 (588562037907/1000000000000 : ℝ) (588562037911/1000000000000 : ℝ) (420861112261/1000000000000 : ℝ) (42086111227/100000000000 : ℝ) (126177893771/250000000000 : ℝ) (504711575091/1000000000000 : ℝ) (3888262287/7812500000 : ℝ) (62212196593/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2089/16384 : ℝ))) 2 (126177893771/250000000000 : ℝ) (504711575091/1000000000000 : ℝ) (3888262287/7812500000 : ℝ) (62212196593/125000000000 : ℝ) (50120457391/100000000000 : ℝ) (250602286959/500000000000 : ℝ) (501192304261/1000000000000 : ℝ) (50119230427/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2089/16384 : ℝ))) 3 (50120457391/100000000000 : ℝ) (250602286959/500000000000 : ℝ) (501192304261/1000000000000 : ℝ) (50119230427/100000000000 : ℝ) (100239687817/200000000000 : ℝ) (250599219547/500000000000 : ℝ) (501198439047/1000000000000 : ℝ) (501198439057/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2089/16384 : ℝ))) 4 (100239687817/200000000000 : ℝ) (250599219547/500000000000 : ℝ) (501198439047/1000000000000 : ℝ) (501198439057/1000000000000 : ℝ) (250599219533/500000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2089/16384 : ℝ))) 5 (250599219533/500000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2089/16384 : ℝ))) 6 (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2089/16384 : ℝ))) 7 (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2089/16384 : ℝ)) hmem 8 (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2089/16384 : ℝ))) hcmem 8 (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2089/16384 : ℝ)) (992078514803/1000000000000 : ℝ) (496039257403/500000000000 : ℝ) (100239687813/200000000000 : ℝ) (125299609769/250000000000 : ℝ) (793566895491/1000000000000 : ℝ) (99195861939/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0775_exp_lower
  have heNumeric : (2054901674131/1000000000000 : ℝ)/4 ≤ Real.exp (-85256494266161/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901674131/1000000000000 : ℝ)/4 ≤ Real.exp ((66847/524288 : ℝ)-(99195861939/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66847/524288 : ℝ) (2089/16384 : ℝ) (99195861939/125000000000 : ℝ) (2054901674131/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0776; no trusted numerical premise.
theorem cover8_leaf0776_exp_radius : (199601945554868917/200000000000000000 : ℝ) ≤ Real.exp ((-66849/4194304 : ℝ)/8) ∧ Real.exp ((-66849/4194304 : ℝ)/8) ≤ (499004863887172293/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66849/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0776_exp_lower : (230028363865940029/250000000000000000 : ℝ) ≤ Real.exp ((-2664265452359/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664265452359/4000000000000 : ℝ)/8) ≤ (920113455463760117/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664265452359/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0776_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490167077/100000000000 : ℝ) ≤ 4*Real.exp (2089/16384 : ℝ)*Real.exp (-mu (radius 8 (66849/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490167077/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66849/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0776_exp_radius
  have hrNumeric : (196837658987/200000000000 : ℝ) ≤ Real.exp (-66849/4194304 : ℝ) ∧ Real.exp (-66849/4194304 : ℝ) ≤ (123023536867/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196837658987/200000000000 : ℝ) ≤ (radius 8 (66849/524288 : ℝ)) ∧ (radius 8 (66849/524288 : ℝ)) ≤ (123023536867/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66849/524288 : ℝ)) (196837658987/200000000000 : ℝ) (123023536867/125000000000 : ℝ) (35425075927/200000000000 : ℝ) (177125379641/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66849/524288 : ℝ)) (196837658987/200000000000 : ℝ) (123023536867/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66849/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196837658987/200000000000 : ℝ) (123023536867/125000000000 : ℝ) (992094147467/1000000000000 : ℝ) (248023536867/250000000000 : ℝ) (496031323339/500000000000 : ℝ) (24801566167/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66849/524288 : ℝ)) 1 (992094147467/1000000000000 : ℝ) (248023536867/250000000000 : ℝ) (496031323339/500000000000 : ℝ) (24801566167/25000000000 : ℝ) (62004899817/62500000000 : ℝ) (496039198537/500000000000 : ℝ) (992078396947/1000000000000 : ℝ) (992078396949/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66849/524288 : ℝ)) 2 (62004899817/62500000000 : ℝ) (496039198537/500000000000 : ℝ) (992078396947/1000000000000 : ℝ) (992078396949/1000000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66849/524288 : ℝ)) 3 (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66849/524288 : ℝ)) 4 (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66849/524288 : ℝ)) 5 (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66849/524288 : ℝ)) 6 (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66849/524288 : ℝ)) 7 (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66849/524288 : ℝ))) (35425075927/200000000000 : ℝ) (177125379641/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66849/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35425075927/200000000000 : ℝ) (177125379641/1000000000000 : ℝ) (588562689817/1000000000000 : ℝ) (588562689821/1000000000000 : ℝ) (336690129/800000000 : ℝ) (210431330629/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66849/524288 : ℝ))) 1 (588562689817/1000000000000 : ℝ) (588562689821/1000000000000 : ℝ) (336690129/800000000 : ℝ) (210431330629/500000000000 : ℝ) (504712675533/1000000000000 : ℝ) (25235633777/50000000000 : ℝ) (248849382131/500000000000 : ℝ) (49769876427/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66849/524288 : ℝ))) 2 (504712675533/1000000000000 : ℝ) (25235633777/50000000000 : ℝ) (248849382131/500000000000 : ℝ) (49769876427/100000000000 : ℝ) (501205719897/1000000000000 : ℝ) (100241143981/200000000000 : ℝ) (100238690119/200000000000 : ℝ) (125298362651/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66849/524288 : ℝ))) 3 (501205719897/1000000000000 : ℝ) (100241143981/200000000000 : ℝ) (100238690119/200000000000 : ℝ) (125298362651/250000000000 : ℝ) (250599792623/500000000000 : ℝ) (100239917051/200000000000 : ℝ) (62649948151/125000000000 : ℝ) (501199585217/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66849/524288 : ℝ))) 4 (250599792623/500000000000 : ℝ) (100239917051/200000000000 : ℝ) (62649948151/125000000000 : ℝ) (501199585217/1000000000000 : ℝ) (501199585227/1000000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66849/524288 : ℝ))) 5 (501199585227/1000000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66849/524288 : ℝ))) 6 (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66849/524288 : ℝ))) 7 (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66849/524288 : ℝ)) hmem 8 (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66849/524288 : ℝ))) hcmem 8 (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66849/524288 : ℝ)) (992078397009/1000000000000 : ℝ) (248019599253/250000000000 : ℝ) (250599792613/500000000000 : ℝ) (125299896309/250000000000 : ℝ) (198392201119/250000000000 : ℝ) (49598050281/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0776_exp_lower
  have heNumeric : (205490167077/100000000000 : ℝ)/4 ≤ Real.exp (-2664265452359/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490167077/100000000000 : ℝ)/4 ≤ Real.exp ((2089/16384 : ℝ)-(49598050281/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2089/16384 : ℝ) (66849/524288 : ℝ) (49598050281/62500000000 : ℝ) (205490167077/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0777; no trusted numerical premise.
theorem cover8_leaf0777_exp_radius : (7984077584250699/8000000000000000 : ℝ) ≤ Real.exp ((-33425/2097152 : ℝ)/8) ∧ Real.exp ((-33425/2097152 : ℝ)/8) ≤ (31187803063479293/31250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33425/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0777_exp_lower : (57507090954858747/62500000000000000 : ℝ) ≤ Real.exp ((-85256494682511/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256494682511/128000000000000 : ℝ)/8) ≤ (920113455277739953/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256494682511/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0777_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901667447/1000000000000 : ℝ) ≤ 4*Real.exp (66849/524288 : ℝ)*Real.exp (-mu (radius 8 (33425/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901667447/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33425/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0777_exp_radius
  have hrNumeric : (492094030143/500000000000 : ℝ) ≤ Real.exp (-33425/2097152 : ℝ) ∧ Real.exp (-33425/2097152 : ℝ) ≤ (984188060287/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492094030143/500000000000 : ℝ) ≤ (radius 8 (33425/262144 : ℝ)) ∧ (radius 8 (33425/262144 : ℝ)) ≤ (984188060287/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33425/262144 : ℝ)) (492094030143/500000000000 : ℝ) (984188060287/1000000000000 : ℝ) (35425336689/200000000000 : ℝ) (44281670863/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33425/262144 : ℝ)) (492094030143/500000000000 : ℝ) (984188060287/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33425/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492094030143/500000000000 : ℝ) (984188060287/1000000000000 : ℝ) (992094030143/1000000000000 : ℝ) (15501469221/15625000000 : ℝ) (198412505683/200000000000 : ℝ) (31001954013/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33425/262144 : ℝ)) 1 (992094030143/1000000000000 : ℝ) (15501469221/15625000000 : ℝ) (198412505683/200000000000 : ℝ) (31001954013/31250000000 : ℝ) (992078279279/1000000000000 : ℝ) (12400978491/12500000000 : ℝ) (992078279153/1000000000000 : ℝ) (198415655831/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33425/262144 : ℝ)) 2 (992078279279/1000000000000 : ℝ) (12400978491/12500000000 : ℝ) (992078279153/1000000000000 : ℝ) (198415655831/200000000000 : ℝ) (62004892451/62500000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33425/262144 : ℝ)) 3 (62004892451/62500000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33425/262144 : ℝ)) 4 (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33425/262144 : ℝ)) 5 (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33425/262144 : ℝ)) 6 (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33425/262144 : ℝ)) 7 (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33425/262144 : ℝ))) (35425336689/200000000000 : ℝ) (44281670863/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33425/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35425336689/200000000000 : ℝ) (44281670863/250000000000 : ℝ) (294281670861/500000000000 : ℝ) (294281670863/500000000000 : ℝ) (420864210221/1000000000000 : ℝ) (42086421023/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33425/262144 : ℝ))) 1 (294281670861/500000000000 : ℝ) (294281670863/500000000000 : ℝ) (420864210221/1000000000000 : ℝ) (42086421023/100000000000 : ℝ) (504713775971/1000000000000 : ℝ) (252356887989/500000000000 : ℝ) (19907998231/40000000000 : ℝ) (497699955783/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33425/262144 : ℝ))) 2 (504713775971/1000000000000 : ℝ) (252356887989/500000000000 : ℝ) (19907998231/40000000000 : ℝ) (497699955783/1000000000000 : ℝ) (501206865873/1000000000000 : ℝ) (501206865881/1000000000000 : ℝ) (250597298459/500000000000 : ℝ) (250597298463/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33425/262144 : ℝ))) 3 (501206865873/1000000000000 : ℝ) (501206865881/1000000000000 : ℝ) (250597298459/500000000000 : ℝ) (250597298463/500000000000 : ℝ) (100240146279/200000000000 : ℝ) (125300182851/250000000000 : ℝ) (501200731357/1000000000000 : ℝ) (250600365683/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33425/262144 : ℝ))) 4 (100240146279/200000000000 : ℝ) (125300182851/250000000000 : ℝ) (501200731357/1000000000000 : ℝ) (250600365683/500000000000 : ℝ) (31325045711/62500000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33425/262144 : ℝ))) 5 (31325045711/62500000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33425/262144 : ℝ))) 6 (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33425/262144 : ℝ))) 7 (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33425/262144 : ℝ)) hmem 8 (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33425/262144 : ℝ))) hcmem 8 (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33425/262144 : ℝ)) (198415655843/200000000000 : ℝ) (496039139609/500000000000 : ℝ) (4009605851/8000000000 : ℝ) (100240146277/200000000000 : ℝ) (793570713443/1000000000000 : ℝ) (396785356731/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0777_exp_lower
  have heNumeric : (2054901667447/1000000000000 : ℝ)/4 ≤ Real.exp (-85256494682511/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901667447/1000000000000 : ℝ)/4 ≤ Real.exp ((66849/524288 : ℝ)-(396785356731/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66849/524288 : ℝ) (33425/262144 : ℝ) (396785356731/500000000000 : ℝ) (2054901667447/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0778; no trusted numerical premise.
theorem cover8_leaf0778_exp_radius : (998009668288331051/1000000000000000000 : ℝ) ≤ Real.exp ((-66851/4194304 : ℝ)/8) ∧ Real.exp ((-66851/4194304 : ℝ)/8) ≤ (249502417072082763/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66851/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0778_exp_lower : (920113455094825171/1000000000000000000 : ℝ) ≤ Real.exp ((-42628247443039/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628247443039/64000000000000 : ℝ)/8) ≤ (230028363773706293/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628247443039/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0778_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901664179/1000000000000 : ℝ) ≤ 4*Real.exp (33425/262144 : ℝ)*Real.exp (-mu (radius 8 (66851/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901664179/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66851/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0778_exp_radius
  have hrNumeric : (492093912819/500000000000 : ℝ) ≤ Real.exp (-66851/4194304 : ℝ) ∧ Real.exp (-66851/4194304 : ℝ) ≤ (984187825639/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492093912819/500000000000 : ℝ) ≤ (radius 8 (66851/524288 : ℝ)) ∧ (radius 8 (66851/524288 : ℝ)) ≤ (984187825639/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66851/524288 : ℝ)) (492093912819/500000000000 : ℝ) (984187825639/1000000000000 : ℝ) (4428199681/25000000000 : ℝ) (177127987247/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66851/524288 : ℝ)) (492093912819/500000000000 : ℝ) (984187825639/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66851/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492093912819/500000000000 : ℝ) (984187825639/1000000000000 : ℝ) (992093912819/1000000000000 : ℝ) (49604695641/50000000000 : ℝ) (124007801269/125000000000 : ℝ) (496031205077/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66851/524288 : ℝ)) 1 (992093912819/1000000000000 : ℝ) (49604695641/50000000000 : ℝ) (124007801269/125000000000 : ℝ) (496031205077/500000000000 : ℝ) (198415632297/200000000000 : ℝ) (992078161487/1000000000000 : ℝ) (12400977017/12500000000 : ℝ) (496039080681/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66851/524288 : ℝ)) 2 (198415632297/200000000000 : ℝ) (992078161487/1000000000000 : ℝ) (12400977017/12500000000 : ℝ) (496039080681/500000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66851/524288 : ℝ)) 3 (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66851/524288 : ℝ)) 4 (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66851/524288 : ℝ)) 5 (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66851/524288 : ℝ)) 6 (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66851/524288 : ℝ)) 7 (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66851/524288 : ℝ))) (4428199681/25000000000 : ℝ) (177127987247/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66851/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4428199681/25000000000 : ℝ) (177127987247/1000000000000 : ℝ) (29428199681/50000000000 : ℝ) (73570499203/125000000000 : ℝ) (420865759167/1000000000000 : ℝ) (420865759177/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66851/524288 : ℝ))) 1 (29428199681/50000000000 : ℝ) (73570499203/125000000000 : ℝ) (420865759167/1000000000000 : ℝ) (420865759177/1000000000000 : ℝ) (504714876393/1000000000000 : ℝ) (504714876401/1000000000000 : ℝ) (497701147269/1000000000000 : ℝ) (497701147277/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66851/524288 : ℝ))) 2 (504714876393/1000000000000 : ℝ) (504714876401/1000000000000 : ℝ) (497701147269/1000000000000 : ℝ) (497701147277/1000000000000 : ℝ) (501208011831/1000000000000 : ℝ) (501208011839/1000000000000 : ℝ) (250597871611/500000000000 : ℝ) (501195743231/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66851/524288 : ℝ))) 3 (501208011831/1000000000000 : ℝ) (501208011839/1000000000000 : ℝ) (250597871611/500000000000 : ℝ) (501195743231/1000000000000 : ℝ) (250600938763/500000000000 : ℝ) (100240375507/200000000000 : ℝ) (31325117343/62500000000 : ℝ) (250600938749/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66851/524288 : ℝ))) 4 (250600938763/500000000000 : ℝ) (100240375507/200000000000 : ℝ) (31325117343/62500000000 : ℝ) (250600938749/500000000000 : ℝ) (501201877507/1000000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66851/524288 : ℝ))) 5 (501201877507/1000000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66851/524288 : ℝ))) 6 (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66851/524288 : ℝ))) 7 (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66851/524288 : ℝ)) hmem 8 (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66851/524288 : ℝ))) hcmem 8 (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66851/524288 : ℝ)) (496039080711/500000000000 : ℝ) (39683126457/40000000000 : ℝ) (250600938753/500000000000 : ℝ) (501201877517/1000000000000 : ℝ) (793572622381/1000000000000 : ℝ) (793572622401/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0778_exp_lower
  have heNumeric : (2054901664179/1000000000000 : ℝ)/4 ≤ Real.exp (-42628247443039/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901664179/1000000000000 : ℝ)/4 ≤ Real.exp ((33425/262144 : ℝ)-(793572622401/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33425/262144 : ℝ) (66851/524288 : ℝ) (793572622401/1000000000000 : ℝ) (2054901664179/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0779; no trusted numerical premise.
theorem cover8_leaf0779_exp_radius : (499004819272662807/500000000000000000 : ℝ) ≤ Real.exp ((-16713/1048576 : ℝ)/8) ∧ Real.exp ((-16713/1048576 : ℝ)/8) ≤ (199601927709065123/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16713/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0779_exp_lower : (460056727456587773/500000000000000000 : ℝ) ≤ Real.exp ((-85256495088237/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256495088237/128000000000000 : ℝ)/8) ≤ (920113454913175547/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256495088237/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0779_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901660933/1000000000000 : ℝ) ≤ 4*Real.exp (66851/524288 : ℝ)*Real.exp (-mu (radius 8 (16713/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901660933/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16713/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0779_exp_radius
  have hrNumeric : (984187590989/1000000000000 : ℝ) ≤ Real.exp (-16713/1048576 : ℝ) ∧ Real.exp (-16713/1048576 : ℝ) ≤ (98418759099/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984187590989/1000000000000 : ℝ) ≤ (radius 8 (16713/131072 : ℝ)) ∧ (radius 8 (16713/131072 : ℝ)) ≤ (98418759099/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16713/131072 : ℝ)) (984187590989/1000000000000 : ℝ) (98418759099/100000000000 : ℝ) (177129291031/1000000000000 : ℝ) (177129291037/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16713/131072 : ℝ)) (984187590989/1000000000000 : ℝ) (98418759099/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16713/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984187590989/1000000000000 : ℝ) (98418759099/100000000000 : ℝ) (496046897747/500000000000 : ℝ) (198418759099/200000000000 : ℝ) (992062291889/1000000000000 : ℝ) (99206229189/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16713/131072 : ℝ)) 1 (496046897747/500000000000 : ℝ) (198418759099/200000000000 : ℝ) (992062291889/1000000000000 : ℝ) (99206229189/100000000000 : ℝ) (992078043691/1000000000000 : ℝ) (992078043693/1000000000000 : ℝ) (496039021783/500000000000 : ℝ) (62004877723/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16713/131072 : ℝ)) 2 (992078043691/1000000000000 : ℝ) (992078043693/1000000000000 : ℝ) (496039021783/500000000000 : ℝ) (62004877723/62500000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16713/131072 : ℝ)) 3 (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16713/131072 : ℝ)) 4 (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16713/131072 : ℝ)) 5 (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16713/131072 : ℝ)) 6 (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16713/131072 : ℝ)) 7 (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16713/131072 : ℝ))) (177129291031/1000000000000 : ℝ) (177129291037/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16713/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177129291031/1000000000000 : ℝ) (177129291037/1000000000000 : ℝ) (117712929103/200000000000 : ℝ) (588564645519/1000000000000 : ℝ) (52608413513/125000000000 : ℝ) (26304206757/62500000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16713/131072 : ℝ))) 1 (117712929103/200000000000 : ℝ) (588564645519/1000000000000 : ℝ) (52608413513/125000000000 : ℝ) (26304206757/62500000000 : ℝ) (504715976809/1000000000000 : ℝ) (31544748551/62500000000 : ℝ) (99540467751/200000000000 : ℝ) (497702338763/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16713/131072 : ℝ))) 2 (504715976809/1000000000000 : ℝ) (31544748551/62500000000 : ℝ) (99540467751/200000000000 : ℝ) (497702338763/1000000000000 : ℝ) (250604578891/500000000000 : ℝ) (50120915779/100000000000 : ℝ) (6264961119/12500000000 : ℝ) (62649611191/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16713/131072 : ℝ))) 3 (250604578891/500000000000 : ℝ) (50120915779/100000000000 : ℝ) (6264961119/12500000000 : ℝ) (62649611191/125000000000 : ℝ) (501203023651/1000000000000 : ℝ) (501203023659/1000000000000 : ℝ) (501203023613/1000000000000 : ℝ) (250601511811/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16713/131072 : ℝ))) 4 (501203023651/1000000000000 : ℝ) (501203023659/1000000000000 : ℝ) (501203023613/1000000000000 : ℝ) (250601511811/500000000000 : ℝ) (31325188977/62500000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16713/131072 : ℝ))) 5 (31325188977/62500000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16713/131072 : ℝ))) 6 (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16713/131072 : ℝ))) 7 (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16713/131072 : ℝ)) hmem 8 (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16713/131072 : ℝ))) hcmem 8 (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16713/131072 : ℝ)) (248019510907/250000000000 : ℝ) (992078043631/1000000000000 : ℝ) (501203023631/1000000000000 : ℝ) (501203023641/1000000000000 : ℝ) (79357453131/100000000000 : ℝ) (793574531329/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0779_exp_lower
  have heNumeric : (2054901660933/1000000000000 : ℝ)/4 ≤ Real.exp (-85256495088237/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901660933/1000000000000 : ℝ)/4 ≤ Real.exp ((66851/524288 : ℝ)-(793574531329/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66851/524288 : ℝ) (16713/131072 : ℝ) (793574531329/1000000000000 : ℝ) (2054901660933/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0780; no trusted numerical premise.
theorem cover8_leaf0780_exp_radius : (998009608802321063/1000000000000000000 : ℝ) ≤ Real.exp ((-66853/4194304 : ℝ)/8) ∧ Real.exp ((-66853/4194304 : ℝ)/8) ≤ (124751201100290133/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66853/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0780_exp_lower : (184022690946765241/200000000000000000 : ℝ) ≤ Real.exp ((-21314123821959/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314123821959/32000000000000 : ℝ)/8) ≤ (460056727366913103/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314123821959/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0780_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901657729/1000000000000 : ℝ) ≤ 4*Real.exp (16713/131072 : ℝ)*Real.exp (-mu (radius 8 (66853/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901657729/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66853/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0780_exp_radius
  have hrNumeric : (49209367817/50000000000 : ℝ) ≤ Real.exp (-66853/4194304 : ℝ) ∧ Real.exp (-66853/4194304 : ℝ) ≤ (984187356341/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49209367817/50000000000 : ℝ) ≤ (radius 8 (66853/524288 : ℝ)) ∧ (radius 8 (66853/524288 : ℝ)) ≤ (984187356341/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66853/524288 : ℝ)) (49209367817/50000000000 : ℝ) (984187356341/1000000000000 : ℝ) (44282648703/250000000000 : ℝ) (88565297409/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66853/524288 : ℝ)) (49209367817/50000000000 : ℝ) (984187356341/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66853/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49209367817/50000000000 : ℝ) (984187356341/1000000000000 : ℝ) (99209367817/100000000000 : ℝ) (992093678171/1000000000000 : ℝ) (496031086813/500000000000 : ℝ) (992062173627/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66853/524288 : ℝ)) 1 (99209367817/100000000000 : ℝ) (992093678171/1000000000000 : ℝ) (496031086813/500000000000 : ℝ) (992062173627/1000000000000 : ℝ) (496038962949/500000000000 : ℝ) (992077925899/1000000000000 : ℝ) (248019481443/250000000000 : ℝ) (496038962887/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66853/524288 : ℝ)) 2 (496038962949/500000000000 : ℝ) (992077925899/1000000000000 : ℝ) (248019481443/250000000000 : ℝ) (496038962887/500000000000 : ℝ) (198415585167/200000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66853/524288 : ℝ)) 3 (198415585167/200000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66853/524288 : ℝ)) 4 (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66853/524288 : ℝ)) 5 (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66853/524288 : ℝ)) 6 (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66853/524288 : ℝ)) 7 (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66853/524288 : ℝ))) (44282648703/250000000000 : ℝ) (88565297409/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66853/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44282648703/250000000000 : ℝ) (88565297409/500000000000 : ℝ) (294282648703/500000000000 : ℝ) (588565297409/1000000000000 : ℝ) (420868857023/1000000000000 : ℝ) (420868857031/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66853/524288 : ℝ))) 1 (294282648703/500000000000 : ℝ) (588565297409/1000000000000 : ℝ) (420868857023/1000000000000 : ℝ) (420868857031/1000000000000 : ℝ) (252358538607/500000000000 : ℝ) (25235853861/50000000000 : ℝ) (497703530229/1000000000000 : ℝ) (124425882559/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66853/524288 : ℝ))) 2 (252358538607/500000000000 : ℝ) (25235853861/50000000000 : ℝ) (497703530229/1000000000000 : ℝ) (124425882559/250000000000 : ℝ) (501210303721/1000000000000 : ℝ) (31325643983/62500000000 : ℝ) (250599017903/500000000000 : ℝ) (501198035813/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66853/524288 : ℝ))) 3 (501210303721/1000000000000 : ℝ) (31325643983/62500000000 : ℝ) (250599017903/500000000000 : ℝ) (501198035813/1000000000000 : ℝ) (501204169763/1000000000000 : ℝ) (501204169771/1000000000000 : ℝ) (20048166789/40000000000 : ℝ) (501204169733/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66853/524288 : ℝ))) 4 (501204169763/1000000000000 : ℝ) (501204169771/1000000000000 : ℝ) (20048166789/40000000000 : ℝ) (501204169733/1000000000000 : ℝ) (31325260609/62500000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66853/524288 : ℝ))) 5 (31325260609/62500000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66853/524288 : ℝ))) 6 (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66853/524288 : ℝ))) 7 (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66853/524288 : ℝ)) hmem 8 (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66853/524288 : ℝ))) hcmem 8 (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66853/524288 : ℝ)) (496038962917/500000000000 : ℝ) (992077925837/1000000000000 : ℝ) (501204169743/1000000000000 : ℝ) (62650521219/125000000000 : ℝ) (39678822011/50000000000 : ℝ) (793576440237/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0780_exp_lower
  have heNumeric : (2054901657729/1000000000000 : ℝ)/4 ≤ Real.exp (-21314123821959/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901657729/1000000000000 : ℝ)/4 ≤ Real.exp ((16713/131072 : ℝ)-(793576440237/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16713/131072 : ℝ) (66853/524288 : ℝ) (793576440237/1000000000000 : ℝ) (2054901657729/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0781; no trusted numerical premise.
theorem cover8_leaf0781_exp_radius : (998009579059317399/1000000000000000000 : ℝ) ≤ Real.exp ((-33427/2097152 : ℝ)/8) ∧ Real.exp ((-33427/2097152 : ℝ)/8) ≤ (4990047895296587/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33427/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0781_exp_lower : (230028363639309301/250000000000000000 : ℝ) ≤ Real.exp ((-85256495484363/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256495484363/128000000000000 : ℝ)/8) ≤ (184022690911447441/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256495484363/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0781_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450827287/500000000000 : ℝ) ≤ 4*Real.exp (66853/524288 : ℝ)*Real.exp (-mu (radius 8 (33427/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450827287/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33427/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0781_exp_radius
  have hrNumeric : (246046780423/250000000000 : ℝ) ≤ Real.exp (-33427/2097152 : ℝ) ∧ Real.exp (-33427/2097152 : ℝ) ≤ (984187121693/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246046780423/250000000000 : ℝ) ≤ (radius 8 (33427/262144 : ℝ)) ∧ (radius 8 (33427/262144 : ℝ)) ≤ (984187121693/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33427/262144 : ℝ)) (246046780423/250000000000 : ℝ) (984187121693/1000000000000 : ℝ) (177131898577/1000000000000 : ℝ) (177131898583/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33427/262144 : ℝ)) (246046780423/250000000000 : ℝ) (984187121693/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33427/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246046780423/250000000000 : ℝ) (984187121693/1000000000000 : ℝ) (496046780423/500000000000 : ℝ) (992093560847/1000000000000 : ℝ) (992062055363/1000000000000 : ℝ) (248015513841/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33427/262144 : ℝ)) 1 (496046780423/500000000000 : ℝ) (992093560847/1000000000000 : ℝ) (992062055363/1000000000000 : ℝ) (248015513841/250000000000 : ℝ) (124009726013/125000000000 : ℝ) (496038904053/500000000000 : ℝ) (992077807979/1000000000000 : ℝ) (992077807981/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33427/262144 : ℝ)) 2 (124009726013/125000000000 : ℝ) (496038904053/500000000000 : ℝ) (992077807979/1000000000000 : ℝ) (992077807981/1000000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33427/262144 : ℝ)) 3 (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33427/262144 : ℝ)) 4 (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33427/262144 : ℝ)) 5 (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33427/262144 : ℝ)) 6 (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33427/262144 : ℝ)) 7 (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33427/262144 : ℝ))) (177131898577/1000000000000 : ℝ) (177131898583/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33427/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177131898577/1000000000000 : ℝ) (177131898583/1000000000000 : ℝ) (73570743661/125000000000 : ℝ) (147141487323/250000000000 : ℝ) (420870405917/1000000000000 : ℝ) (16834816237/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33427/262144 : ℝ))) 1 (73570743661/125000000000 : ℝ) (147141487323/250000000000 : ℝ) (420870405917/1000000000000 : ℝ) (16834816237/40000000000 : ℝ) (252359088801/500000000000 : ℝ) (504718177609/1000000000000 : ℝ) (497704721683/1000000000000 : ℝ) (49770472169/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33427/262144 : ℝ))) 2 (252359088801/500000000000 : ℝ) (504718177609/1000000000000 : ℝ) (497704721683/1000000000000 : ℝ) (49770472169/100000000000 : ℝ) (250605724821/500000000000 : ℝ) (10024228993/20000000000 : ℝ) (250599591037/500000000000 : ℝ) (250599591041/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33427/262144 : ℝ))) 3 (250605724821/500000000000 : ℝ) (10024228993/20000000000 : ℝ) (250599591037/500000000000 : ℝ) (250599591041/500000000000 : ℝ) (250602657929/500000000000 : ℝ) (250602657933/500000000000 : ℝ) (25060265791/50000000000 : ℝ) (501205315829/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33427/262144 : ℝ))) 4 (250602657929/500000000000 : ℝ) (250602657933/500000000000 : ℝ) (25060265791/50000000000 : ℝ) (501205315829/1000000000000 : ℝ) (501205315839/1000000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33427/262144 : ℝ))) 5 (501205315839/1000000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33427/262144 : ℝ))) 6 (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33427/262144 : ℝ))) 7 (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33427/262144 : ℝ)) hmem 8 (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33427/262144 : ℝ))) hcmem 8 (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33427/262144 : ℝ)) (992077808041/1000000000000 : ℝ) (248019452011/250000000000 : ℝ) (250602657919/500000000000 : ℝ) (62650664481/125000000000 : ℝ) (396789174551/500000000000 : ℝ) (793578349121/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0781_exp_lower
  have heNumeric : (1027450827287/500000000000 : ℝ)/4 ≤ Real.exp (-85256495484363/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450827287/500000000000 : ℝ)/4 ≤ Real.exp ((66853/524288 : ℝ)-(793578349121/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66853/524288 : ℝ) (33427/262144 : ℝ) (793578349121/1000000000000 : ℝ) (1027450827287/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0782; no trusted numerical premise.
theorem cover8_leaf0782_exp_radius : (998009549316314621/1000000000000000000 : ℝ) ≤ Real.exp ((-66855/4194304 : ℝ)/8) ∧ Real.exp ((-66855/4194304 : ℝ)/8) ≤ (499004774658157311/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66855/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0782_exp_lower : (230028363595535847/250000000000000000 : ℝ) ≤ Real.exp ((-42628247839613/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628247839613/64000000000000 : ℝ)/8) ≤ (920113454382143389/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628247839613/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0782_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450825723/500000000000 : ℝ) ≤ 4*Real.exp (33427/262144 : ℝ)*Real.exp (-mu (radius 8 (66855/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450825723/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66855/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0782_exp_radius
  have hrNumeric : (984186887043/1000000000000 : ℝ) ≤ Real.exp (-66855/4194304 : ℝ) ∧ Real.exp (-66855/4194304 : ℝ) ≤ (246046721761/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984186887043/1000000000000 : ℝ) ≤ (radius 8 (66855/524288 : ℝ)) ∧ (radius 8 (66855/524288 : ℝ)) ≤ (246046721761/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66855/524288 : ℝ)) (984186887043/1000000000000 : ℝ) (246046721761/250000000000 : ℝ) (88566601169/500000000000 : ℝ) (22141650293/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66855/524288 : ℝ)) (984186887043/1000000000000 : ℝ) (246046721761/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66855/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984186887043/1000000000000 : ℝ) (246046721761/250000000000 : ℝ) (992093443521/1000000000000 : ℝ) (496046721761/500000000000 : ℝ) (9920619371/10000000000 : ℝ) (992061937101/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66855/524288 : ℝ)) 1 (992093443521/1000000000000 : ℝ) (496046721761/500000000000 : ℝ) (9920619371/10000000000 : ℝ) (992061937101/1000000000000 : ℝ) (99207769031/100000000000 : ℝ) (124009711289/125000000000 : ℝ) (198415538037/200000000000 : ℝ) (992077690187/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66855/524288 : ℝ)) 2 (99207769031/100000000000 : ℝ) (124009711289/125000000000 : ℝ) (198415538037/200000000000 : ℝ) (992077690187/1000000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66855/524288 : ℝ)) 3 (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66855/524288 : ℝ)) 4 (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66855/524288 : ℝ)) 5 (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66855/524288 : ℝ)) 6 (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66855/524288 : ℝ)) 7 (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66855/524288 : ℝ))) (88566601169/500000000000 : ℝ) (22141650293/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66855/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88566601169/500000000000 : ℝ) (22141650293/125000000000 : ℝ) (588566601169/1000000000000 : ℝ) (147141650293/250000000000 : ℝ) (1052179887/2500000000 : ℝ) (420871954809/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66855/524288 : ℝ))) 1 (588566601169/1000000000000 : ℝ) (147141650293/250000000000 : ℝ) (1052179887/2500000000 : ℝ) (420871954809/1000000000000 : ℝ) (15772477437/31250000000 : ℝ) (504719277991/1000000000000 : ℝ) (497705913129/1000000000000 : ℝ) (497705913137/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66855/524288 : ℝ))) 2 (15772477437/31250000000 : ℝ) (504719277991/1000000000000 : ℝ) (497705913129/1000000000000 : ℝ) (497705913137/1000000000000 : ℝ) (125303148889/250000000000 : ℝ) (125303148891/250000000000 : ℝ) (250600164167/500000000000 : ℝ) (501200328343/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66855/524288 : ℝ))) 3 (125303148889/250000000000 : ℝ) (125303148891/250000000000 : ℝ) (250600164167/500000000000 : ℝ) (501200328343/1000000000000 : ℝ) (100241292389/200000000000 : ℝ) (250603230977/500000000000 : ℝ) (501206461907/1000000000000 : ℝ) (125301615479/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66855/524288 : ℝ))) 4 (100241292389/200000000000 : ℝ) (250603230977/500000000000 : ℝ) (501206461907/1000000000000 : ℝ) (125301615479/250000000000 : ℝ) (250603230963/500000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66855/524288 : ℝ))) 5 (250603230963/500000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66855/524288 : ℝ))) 6 (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66855/524288 : ℝ))) 7 (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66855/524288 : ℝ)) hmem 8 (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66855/524288 : ℝ))) hcmem 8 (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66855/524288 : ℝ)) (992077690247/1000000000000 : ℝ) (3968310761/4000000000 : ℝ) (20048258477/40000000000 : ℝ) (100241292387/200000000000 : ℝ) (198395064493/250000000000 : ℝ) (99197532249/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0782_exp_lower
  have heNumeric : (1027450825723/500000000000 : ℝ)/4 ≤ Real.exp (-42628247839613/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450825723/500000000000 : ℝ)/4 ≤ Real.exp ((33427/262144 : ℝ)-(99197532249/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33427/262144 : ℝ) (66855/524288 : ℝ) (99197532249/125000000000 : ℝ) (1027450825723/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0783; no trusted numerical premise.
theorem cover8_leaf0783_exp_radius : (99800951957331273/100000000000000000 : ℝ) ≤ Real.exp ((-8357/524288 : ℝ)/8) ∧ Real.exp ((-8357/524288 : ℝ)/8) ≤ (998009519573312731/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8357/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0783_exp_lower : (460056727105077477/500000000000000000 : ℝ) ≤ Real.exp ((-85256495870633/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256495870633/128000000000000 : ℝ)/8) ≤ (184022690842030991/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256495870633/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0783_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901648373/1000000000000 : ℝ) ≤ 4*Real.exp (66855/524288 : ℝ)*Real.exp (-mu (radius 8 (8357/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901648373/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8357/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0783_exp_radius
  have hrNumeric : (196837330479/200000000000 : ℝ) ≤ Real.exp (-8357/524288 : ℝ) ∧ Real.exp (-8357/524288 : ℝ) ≤ (246046663099/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196837330479/200000000000 : ℝ) ≤ (radius 8 (8357/65536 : ℝ)) ∧ (radius 8 (8357/65536 : ℝ)) ≤ (246046663099/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8357/65536 : ℝ)) (196837330479/200000000000 : ℝ) (246046663099/250000000000 : ℝ) (177134506083/1000000000000 : ℝ) (17713450609/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8357/65536 : ℝ)) (196837330479/200000000000 : ℝ) (246046663099/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8357/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196837330479/200000000000 : ℝ) (246046663099/250000000000 : ℝ) (992093326197/1000000000000 : ℝ) (496046663099/500000000000 : ℝ) (992061818837/1000000000000 : ℝ) (496030909419/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8357/65536 : ℝ)) 1 (992093326197/1000000000000 : ℝ) (496046663099/500000000000 : ℝ) (992061818837/1000000000000 : ℝ) (496030909419/500000000000 : ℝ) (992077572517/1000000000000 : ℝ) (496038786259/500000000000 : ℝ) (992077572391/1000000000000 : ℝ) (992077572393/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8357/65536 : ℝ)) 2 (992077572517/1000000000000 : ℝ) (496038786259/500000000000 : ℝ) (992077572391/1000000000000 : ℝ) (992077572393/1000000000000 : ℝ) (496038786227/500000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8357/65536 : ℝ)) 3 (496038786227/500000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8357/65536 : ℝ)) 4 (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8357/65536 : ℝ)) 5 (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8357/65536 : ℝ)) 6 (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8357/65536 : ℝ)) 7 (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8357/65536 : ℝ))) (177134506083/1000000000000 : ℝ) (17713450609/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8357/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177134506083/1000000000000 : ℝ) (17713450609/100000000000 : ℝ) (588567253041/1000000000000 : ℝ) (117713450609/200000000000 : ℝ) (420873503659/1000000000000 : ℝ) (420873503669/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8357/65536 : ℝ))) 1 (588567253041/1000000000000 : ℝ) (117713450609/200000000000 : ℝ) (420873503659/1000000000000 : ℝ) (420873503669/1000000000000 : ℝ) (10094407567/20000000000 : ℝ) (504720378357/1000000000000 : ℝ) (124426776139/250000000000 : ℝ) (99541420913/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8357/65536 : ℝ))) 2 (10094407567/20000000000 : ℝ) (504720378357/1000000000000 : ℝ) (124426776139/250000000000 : ℝ) (99541420913/200000000000 : ℝ) (501213741453/1000000000000 : ℝ) (501213741461/1000000000000 : ℝ) (501201474577/1000000000000 : ℝ) (250600737293/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8357/65536 : ℝ))) 3 (501213741453/1000000000000 : ℝ) (501213741461/1000000000000 : ℝ) (501201474577/1000000000000 : ℝ) (250600737293/500000000000 : ℝ) (100241521603/200000000000 : ℝ) (62650951003/125000000000 : ℝ) (501207607977/1000000000000 : ℝ) (250603803993/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8357/65536 : ℝ))) 4 (100241521603/200000000000 : ℝ) (62650951003/125000000000 : ℝ) (501207607977/1000000000000 : ℝ) (250603803993/500000000000 : ℝ) (125301901999/250000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8357/65536 : ℝ))) 5 (125301901999/250000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8357/65536 : ℝ))) 6 (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8357/65536 : ℝ))) 7 (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8357/65536 : ℝ)) hmem 8 (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8357/65536 : ℝ))) hcmem 8 (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8357/65536 : ℝ)) (992077572453/1000000000000 : ℝ) (124009696557/125000000000 : ℝ) (100241521599/200000000000 : ℝ) (100241521601/200000000000 : ℝ) (793582166817/1000000000000 : ℝ) (198395541709/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0783_exp_lower
  have heNumeric : (2054901648373/1000000000000 : ℝ)/4 ≤ Real.exp (-85256495870633/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901648373/1000000000000 : ℝ)/4 ≤ Real.exp ((66855/524288 : ℝ)-(198395541709/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66855/524288 : ℝ) (8357/65536 : ℝ) (198395541709/250000000000 : ℝ) (2054901648373/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0784; no trusted numerical premise.
theorem cover8_leaf0784_exp_radius : (249502372457577931/250000000000000000 : ℝ) ≤ Real.exp ((-66857/4194304 : ℝ)/8) ∧ Real.exp ((-66857/4194304 : ℝ)/8) ≤ (39920379593212469/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66857/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0784_exp_lower : (92011345404035179/100000000000000000 : ℝ) ≤ Real.exp ((-10657062007451/16000000000000 : ℝ)/8) ∧ Real.exp ((-10657062007451/16000000000000 : ℝ)/8) ≤ (920113454040351791/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10657062007451/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0784_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901645339/1000000000000 : ℝ) ≤ 4*Real.exp (8357/65536 : ℝ)*Real.exp (-mu (radius 8 (66857/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901645339/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66857/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0784_exp_radius
  have hrNumeric : (984186417747/1000000000000 : ℝ) ≤ Real.exp (-66857/4194304 : ℝ) ∧ Real.exp (-66857/4194304 : ℝ) ≤ (246046604437/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984186417747/1000000000000 : ℝ) ≤ (radius 8 (66857/524288 : ℝ)) ∧ (radius 8 (66857/524288 : ℝ)) ≤ (246046604437/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66857/524288 : ℝ)) (984186417747/1000000000000 : ℝ) (246046604437/250000000000 : ℝ) (177135809819/1000000000000 : ℝ) (7085432393/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66857/524288 : ℝ)) (984186417747/1000000000000 : ℝ) (246046604437/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66857/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984186417747/1000000000000 : ℝ) (246046604437/250000000000 : ℝ) (992093208873/1000000000000 : ℝ) (496046604437/500000000000 : ℝ) (496030850287/500000000000 : ℝ) (31001928143/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66857/524288 : ℝ)) 1 (992093208873/1000000000000 : ℝ) (496046604437/500000000000 : ℝ) (496030850287/500000000000 : ℝ) (31001928143/31250000000 : ℝ) (992077454723/1000000000000 : ℝ) (39683098189/40000000000 : ℝ) (496038727299/500000000000 : ℝ) (4960387273/5000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66857/524288 : ℝ)) 2 (992077454723/1000000000000 : ℝ) (39683098189/40000000000 : ℝ) (496038727299/500000000000 : ℝ) (4960387273/5000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66857/524288 : ℝ)) 3 (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66857/524288 : ℝ)) 4 (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66857/524288 : ℝ)) 5 (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66857/524288 : ℝ)) 6 (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66857/524288 : ℝ)) 7 (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66857/524288 : ℝ))) (177135809819/1000000000000 : ℝ) (7085432393/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66857/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177135809819/1000000000000 : ℝ) (7085432393/40000000000 : ℝ) (588567904909/1000000000000 : ℝ) (588567904913/1000000000000 : ℝ) (210437526251/500000000000 : ℝ) (42087505251/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66857/524288 : ℝ))) 1 (588567904909/1000000000000 : ℝ) (588567904913/1000000000000 : ℝ) (210437526251/500000000000 : ℝ) (42087505251/100000000000 : ℝ) (100944295741/200000000000 : ℝ) (63090184839/125000000000 : ℝ) (124427073993/250000000000 : ℝ) (497708295979/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66857/524288 : ℝ))) 2 (100944295741/200000000000 : ℝ) (63090184839/125000000000 : ℝ) (124427073993/250000000000 : ℝ) (497708295979/1000000000000 : ℝ) (250607443669/500000000000 : ℝ) (250607443673/500000000000 : ℝ) (501202620809/1000000000000 : ℝ) (501202620817/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66857/524288 : ℝ))) 3 (250607443669/500000000000 : ℝ) (250607443673/500000000000 : ℝ) (501202620809/1000000000000 : ℝ) (501202620817/1000000000000 : ℝ) (501208754073/1000000000000 : ℝ) (250604377041/500000000000 : ℝ) (100241750807/200000000000 : ℝ) (125302188511/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66857/524288 : ℝ))) 4 (501208754073/1000000000000 : ℝ) (250604377041/500000000000 : ℝ) (100241750807/200000000000 : ℝ) (125302188511/250000000000 : ℝ) (250604377027/500000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66857/524288 : ℝ))) 5 (250604377027/500000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66857/524288 : ℝ))) 6 (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66857/524288 : ℝ))) 7 (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66857/524288 : ℝ)) hmem 8 (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66857/524288 : ℝ))) hcmem 8 (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66857/524288 : ℝ)) (49603872733/50000000000 : ℝ) (992077454663/1000000000000 : ℝ) (501208754053/1000000000000 : ℝ) (501208754063/1000000000000 : ℝ) (793584075641/1000000000000 : ℝ) (793584075661/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0784_exp_lower
  have heNumeric : (2054901645339/1000000000000 : ℝ)/4 ≤ Real.exp (-10657062007451/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901645339/1000000000000 : ℝ)/4 ≤ Real.exp ((8357/65536 : ℝ)-(793584075661/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8357/65536 : ℝ) (66857/524288 : ℝ) (793584075661/1000000000000 : ℝ) (2054901645339/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0785; no trusted numerical premise.
theorem cover8_leaf0785_exp_radius : (499004730043655803/500000000000000000 : ℝ) ≤ Real.exp ((-33429/2097152 : ℝ)/8) ∧ Real.exp ((-33429/2097152 : ℝ)/8) ≤ (998009460087311607/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33429/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0785_exp_lower : (460056726935791877/500000000000000000 : ℝ) ≤ Real.exp ((-85256496247431/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256496247431/128000000000000 : ℝ)/8) ≤ (184022690774316751/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256496247431/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0785_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725410581/250000000000 : ℝ) ≤ 4*Real.exp (66857/524288 : ℝ)*Real.exp (-mu (radius 8 (33429/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725410581/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33429/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0785_exp_radius
  have hrNumeric : (492093091549/500000000000 : ℝ) ≤ Real.exp (-33429/2097152 : ℝ) ∧ Real.exp (-33429/2097152 : ℝ) ≤ (984186183099/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492093091549/500000000000 : ℝ) ≤ (radius 8 (33429/262144 : ℝ)) ∧ (radius 8 (33429/262144 : ℝ)) ≤ (984186183099/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33429/262144 : ℝ)) (492093091549/500000000000 : ℝ) (984186183099/1000000000000 : ℝ) (3542742271/20000000000 : ℝ) (177137113557/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33429/262144 : ℝ)) (492093091549/500000000000 : ℝ) (984186183099/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33429/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492093091549/500000000000 : ℝ) (984186183099/1000000000000 : ℝ) (992093091549/1000000000000 : ℝ) (19841861831/20000000000 : ℝ) (992061582311/1000000000000 : ℝ) (124007697789/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33429/262144 : ℝ)) 1 (992093091549/1000000000000 : ℝ) (19841861831/20000000000 : ℝ) (992061582311/1000000000000 : ℝ) (124007697789/125000000000 : ℝ) (99207733693/100000000000 : ℝ) (992077336931/1000000000000 : ℝ) (248019334201/250000000000 : ℝ) (496038668403/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33429/262144 : ℝ)) 2 (99207733693/100000000000 : ℝ) (992077336931/1000000000000 : ℝ) (248019334201/250000000000 : ℝ) (496038668403/500000000000 : ℝ) (992077336867/1000000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33429/262144 : ℝ)) 3 (992077336867/1000000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33429/262144 : ℝ)) 4 (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33429/262144 : ℝ)) 5 (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33429/262144 : ℝ)) 6 (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33429/262144 : ℝ)) 7 (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33429/262144 : ℝ))) (3542742271/20000000000 : ℝ) (177137113557/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33429/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3542742271/20000000000 : ℝ) (177137113557/1000000000000 : ℝ) (23542742271/40000000000 : ℝ) (588568556779/1000000000000 : ℝ) (420876601333/1000000000000 : ℝ) (210438300671/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33429/262144 : ℝ))) 1 (23542742271/40000000000 : ℝ) (588568556779/1000000000000 : ℝ) (420876601333/1000000000000 : ℝ) (210438300671/500000000000 : ℝ) (252361289527/500000000000 : ℝ) (504722579061/1000000000000 : ℝ) (248854743689/500000000000 : ℝ) (248854743693/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33429/262144 : ℝ))) 2 (252361289527/500000000000 : ℝ) (504722579061/1000000000000 : ℝ) (248854743689/500000000000 : ℝ) (248854743693/500000000000 : ℝ) (7831500519/15625000000 : ℝ) (62652004153/125000000000 : ℝ) (501203767033/1000000000000 : ℝ) (250601883521/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33429/262144 : ℝ))) 3 (7831500519/15625000000 : ℝ) (62652004153/125000000000 : ℝ) (501203767033/1000000000000 : ℝ) (250601883521/500000000000 : ℝ) (125302475031/250000000000 : ℝ) (501209900133/1000000000000 : ℝ) (250604950043/500000000000 : ℝ) (7831404689/15625000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33429/262144 : ℝ))) 4 (125302475031/250000000000 : ℝ) (501209900133/1000000000000 : ℝ) (250604950043/500000000000 : ℝ) (7831404689/15625000000 : ℝ) (100241980021/200000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33429/262144 : ℝ))) 5 (100241980021/200000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33429/262144 : ℝ))) 6 (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33429/262144 : ℝ))) 7 (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33429/262144 : ℝ)) hmem 8 (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33429/262144 : ℝ))) hcmem 8 (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33429/262144 : ℝ)) (496038668433/500000000000 : ℝ) (992077336869/1000000000000 : ℝ) (62651237513/125000000000 : ℝ) (100241980023/200000000000 : ℝ) (99198248057/125000000000 : ℝ) (793585984477/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0785_exp_lower
  have heNumeric : (513725410581/250000000000 : ℝ)/4 ≤ Real.exp (-85256496247431/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725410581/250000000000 : ℝ)/4 ≤ Real.exp ((66857/524288 : ℝ)-(793585984477/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66857/524288 : ℝ) (33429/262144 : ℝ) (793585984477/1000000000000 : ℝ) (513725410581/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0786; no trusted numerical premise.
theorem cover8_leaf0786_exp_radius : (499004715172156187/500000000000000000 : ℝ) ≤ Real.exp ((-66859/4194304 : ℝ)/8) ∧ Real.exp ((-66859/4194304 : ℝ)/8) ≤ (7984075442754499/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66859/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0786_exp_lower : (920113453706381157/1000000000000000000 : ℝ) ≤ Real.exp ((-42628248215643/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628248215643/64000000000000 : ℝ)/8) ≤ (460056726853190579/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628248215643/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0786_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725409843/250000000000 : ℝ) ≤ 4*Real.exp (33429/262144 : ℝ)*Real.exp (-mu (radius 8 (66859/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (513725409843/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66859/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0786_exp_radius
  have hrNumeric : (19683718969/20000000000 : ℝ) ≤ Real.exp (-66859/4194304 : ℝ) ∧ Real.exp (-66859/4194304 : ℝ) ≤ (984185948451/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19683718969/20000000000 : ℝ) ≤ (radius 8 (66859/524288 : ℝ)) ∧ (radius 8 (66859/524288 : ℝ)) ≤ (984185948451/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66859/524288 : ℝ)) (19683718969/20000000000 : ℝ) (984185948451/1000000000000 : ℝ) (88569208633/500000000000 : ℝ) (22142302159/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66859/524288 : ℝ)) (19683718969/20000000000 : ℝ) (984185948451/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66859/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19683718969/20000000000 : ℝ) (984185948451/1000000000000 : ℝ) (39683718969/40000000000 : ℝ) (496046487113/500000000000 : ℝ) (62003841503/62500000000 : ℝ) (992061464049/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66859/524288 : ℝ)) 1 (39683718969/40000000000 : ℝ) (496046487113/500000000000 : ℝ) (62003841503/62500000000 : ℝ) (992061464049/1000000000000 : ℝ) (15501206549/15625000000 : ℝ) (496038609569/500000000000 : ℝ) (992077219011/1000000000000 : ℝ) (992077219013/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66859/524288 : ℝ)) 2 (15501206549/15625000000 : ℝ) (496038609569/500000000000 : ℝ) (992077219011/1000000000000 : ℝ) (992077219013/1000000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66859/524288 : ℝ)) 3 (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66859/524288 : ℝ)) 4 (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66859/524288 : ℝ)) 5 (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66859/524288 : ℝ)) 6 (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66859/524288 : ℝ)) 7 (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66859/524288 : ℝ))) (88569208633/500000000000 : ℝ) (22142302159/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66859/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88569208633/500000000000 : ℝ) (22142302159/125000000000 : ℝ) (588569208633/1000000000000 : ℝ) (147142302159/250000000000 : ℝ) (21043907507/50000000000 : ℝ) (105219537537/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66859/524288 : ℝ))) 1 (588569208633/1000000000000 : ℝ) (147142302159/250000000000 : ℝ) (21043907507/50000000000 : ℝ) (105219537537/250000000000 : ℝ) (252361839693/500000000000 : ℝ) (15772614981/31250000000 : ℝ) (497710678767/1000000000000 : ℝ) (248855339387/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66859/524288 : ℝ))) 2 (252361839693/500000000000 : ℝ) (15772614981/31250000000 : ℝ) (497710678767/1000000000000 : ℝ) (248855339387/500000000000 : ℝ) (125304294769/250000000000 : ℝ) (501217179083/1000000000000 : ℝ) (501204913241/1000000000000 : ℝ) (15662653539/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66859/524288 : ℝ))) 3 (125304294769/250000000000 : ℝ) (501217179083/1000000000000 : ℝ) (501204913241/1000000000000 : ℝ) (15662653539/31250000000 : ℝ) (250605523079/500000000000 : ℝ) (250605523083/500000000000 : ℝ) (12530276153/25000000000 : ℝ) (31325690383/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66859/524288 : ℝ))) 4 (250605523079/500000000000 : ℝ) (250605523083/500000000000 : ℝ) (12530276153/25000000000 : ℝ) (31325690383/62500000000 : ℝ) (501211046139/1000000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66859/524288 : ℝ))) 5 (501211046139/1000000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66859/524288 : ℝ))) 6 (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66859/524288 : ℝ))) 7 (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66859/524288 : ℝ)) hmem 8 (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66859/524288 : ℝ))) hcmem 8 (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66859/524288 : ℝ)) (992077219073/1000000000000 : ℝ) (248019304769/250000000000 : ℝ) (250605523069/500000000000 : ℝ) (501211046147/1000000000000 : ℝ) (198396973311/250000000000 : ℝ) (396793946631/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0786_exp_lower
  have heNumeric : (513725409843/250000000000 : ℝ)/4 ≤ Real.exp (-42628248215643/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725409843/250000000000 : ℝ)/4 ≤ Real.exp ((33429/262144 : ℝ)-(396793946631/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33429/262144 : ℝ) (66859/524288 : ℝ) (396793946631/500000000000 : ℝ) (513725409843/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0787; no trusted numerical premise.
theorem cover8_leaf0787_exp_radius : (249502350150328507/250000000000000000 : ℝ) ≤ Real.exp ((-16715/1048576 : ℝ)/8) ∧ Real.exp ((-16715/1048576 : ℝ)/8) ≤ (998009400601314029/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16715/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0787_exp_lower : (920113453542903773/1000000000000000000 : ℝ) ≤ Real.exp ((-85256496613221/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256496613221/128000000000000 : ℝ)/8) ≤ (460056726771451887/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256496613221/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0787_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901636451/1000000000000 : ℝ) ≤ 4*Real.exp (66859/524288 : ℝ)*Real.exp (-mu (radius 8 (16715/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901636451/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16715/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0787_exp_radius
  have hrNumeric : (492092856901/500000000000 : ℝ) ≤ Real.exp (-16715/1048576 : ℝ) ∧ Real.exp (-16715/1048576 : ℝ) ≤ (984185713803/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492092856901/500000000000 : ℝ) ≤ (radius 8 (16715/131072 : ℝ)) ∧ (radius 8 (16715/131072 : ℝ)) ≤ (984185713803/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16715/131072 : ℝ)) (492092856901/500000000000 : ℝ) (984185713803/1000000000000 : ℝ) (44284930243/250000000000 : ℝ) (88569860489/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16715/131072 : ℝ)) (492092856901/500000000000 : ℝ) (984185713803/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16715/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492092856901/500000000000 : ℝ) (984185713803/1000000000000 : ℝ) (992092856901/1000000000000 : ℝ) (496046428451/500000000000 : ℝ) (198412269157/200000000000 : ℝ) (992061345787/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16715/131072 : ℝ)) 1 (992092856901/1000000000000 : ℝ) (496046428451/500000000000 : ℝ) (198412269157/200000000000 : ℝ) (992061345787/1000000000000 : ℝ) (992077101343/1000000000000 : ℝ) (198415420269/200000000000 : ℝ) (992077101217/1000000000000 : ℝ) (49603855061/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16715/131072 : ℝ)) 2 (992077101343/1000000000000 : ℝ) (198415420269/200000000000 : ℝ) (992077101217/1000000000000 : ℝ) (49603855061/50000000000 : ℝ) (6200481883/6250000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16715/131072 : ℝ)) 3 (6200481883/6250000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16715/131072 : ℝ)) 4 (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16715/131072 : ℝ)) 5 (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16715/131072 : ℝ)) 6 (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16715/131072 : ℝ)) 7 (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16715/131072 : ℝ))) (44284930243/250000000000 : ℝ) (88569860489/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16715/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44284930243/250000000000 : ℝ) (88569860489/500000000000 : ℝ) (294284930243/500000000000 : ℝ) (588569860489/1000000000000 : ℝ) (42087969893/100000000000 : ℝ) (210439849469/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16715/131072 : ℝ))) 1 (294284930243/500000000000 : ℝ) (588569860489/1000000000000 : ℝ) (42087969893/100000000000 : ℝ) (210439849469/500000000000 : ℝ) (126181194927/250000000000 : ℝ) (252362389857/500000000000 : ℝ) (248855935071/500000000000 : ℝ) (497711870149/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16715/131072 : ℝ))) 2 (126181194927/250000000000 : ℝ) (252362389857/500000000000 : ℝ) (248855935071/500000000000 : ℝ) (497711870149/1000000000000 : ℝ) (20048732997/40000000000 : ℝ) (125304581233/250000000000 : ℝ) (125301514859/250000000000 : ℝ) (501206059443/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16715/131072 : ℝ))) 3 (20048732997/40000000000 : ℝ) (125304581233/250000000000 : ℝ) (125301514859/250000000000 : ℝ) (501206059443/1000000000000 : ℝ) (25060609609/50000000000 : ℝ) (125303048047/250000000000 : ℝ) (250606096071/500000000000 : ℝ) (10024243843/20000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16715/131072 : ℝ))) 4 (25060609609/50000000000 : ℝ) (125303048047/250000000000 : ℝ) (250606096071/500000000000 : ℝ) (10024243843/20000000000 : ℝ) (501212192161/1000000000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16715/131072 : ℝ))) 5 (501212192161/1000000000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16715/131072 : ℝ))) 6 (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16715/131072 : ℝ))) 7 (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16715/131072 : ℝ)) hmem 8 (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16715/131072 : ℝ))) hcmem 8 (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16715/131072 : ℝ)) (992077101279/1000000000000 : ℝ) (992077101283/1000000000000 : ℝ) (3132576201/6250000000 : ℝ) (501212192169/1000000000000 : ℝ) (793589802013/1000000000000 : ℝ) (49599362627/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0787_exp_lower
  have heNumeric : (2054901636451/1000000000000 : ℝ)/4 ≤ Real.exp (-85256496613221/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901636451/1000000000000 : ℝ)/4 ≤ Real.exp ((66859/524288 : ℝ)-(49599362627/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66859/524288 : ℝ) (16715/131072 : ℝ) (49599362627/62500000000 : ℝ) (2054901636451/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0788; no trusted numerical premise.
theorem cover8_leaf0788_exp_radius : (124751171357289571/125000000000000000 : ℝ) ≤ Real.exp ((-66861/4194304 : ℝ)/8) ∧ Real.exp ((-66861/4194304 : ℝ)/8) ≤ (998009370858316569/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66861/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0788_exp_lower : (920113453381611659/1000000000000000000 : ℝ) ≤ Real.exp ((-21314124198181/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314124198181/32000000000000 : ℝ)/8) ≤ (46005672669080583/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314124198181/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0788_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (205490163357/100000000000 : ℝ) ≤ 4*Real.exp (16715/131072 : ℝ)*Real.exp (-mu (radius 8 (66861/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (205490163357/100000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66861/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0788_exp_radius
  have hrNumeric : (492092739577/500000000000 : ℝ) ≤ Real.exp (-66861/4194304 : ℝ) ∧ Real.exp (-66861/4194304 : ℝ) ≤ (196837095831/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492092739577/500000000000 : ℝ) ≤ (radius 8 (66861/524288 : ℝ)) ∧ (radius 8 (66861/524288 : ℝ)) ≤ (196837095831/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66861/524288 : ℝ)) (492092739577/500000000000 : ℝ) (196837095831/200000000000 : ℝ) (44285256167/250000000000 : ℝ) (88570512337/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66861/524288 : ℝ)) (492092739577/500000000000 : ℝ) (196837095831/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66861/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492092739577/500000000000 : ℝ) (196837095831/200000000000 : ℝ) (992092739577/1000000000000 : ℝ) (496046369789/500000000000 : ℝ) (496030613761/500000000000 : ℝ) (248015306881/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66861/524288 : ℝ)) 1 (992092739577/1000000000000 : ℝ) (496046369789/500000000000 : ℝ) (496030613761/500000000000 : ℝ) (248015306881/250000000000 : ℝ) (992076983549/1000000000000 : ℝ) (992076983551/1000000000000 : ℝ) (7750601433/7812500000 : ℝ) (496038491713/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66861/524288 : ℝ)) 2 (992076983549/1000000000000 : ℝ) (992076983551/1000000000000 : ℝ) (7750601433/7812500000 : ℝ) (496038491713/500000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66861/524288 : ℝ)) 3 (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66861/524288 : ℝ)) 4 (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66861/524288 : ℝ)) 5 (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66861/524288 : ℝ)) 6 (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66861/524288 : ℝ)) 7 (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66861/524288 : ℝ))) (44285256167/250000000000 : ℝ) (88570512337/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66861/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44285256167/250000000000 : ℝ) (88570512337/500000000000 : ℝ) (294285256167/500000000000 : ℝ) (588570512337/1000000000000 : ℝ) (210440623851/500000000000 : ℝ) (420881247711/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66861/524288 : ℝ))) 1 (294285256167/500000000000 : ℝ) (588570512337/1000000000000 : ℝ) (210440623851/500000000000 : ℝ) (420881247711/1000000000000 : ℝ) (252362940009/500000000000 : ℝ) (63090735003/125000000000 : ℝ) (3888383293/7812500000 : ℝ) (497713061511/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66861/524288 : ℝ))) 2 (252362940009/500000000000 : ℝ) (63090735003/125000000000 : ℝ) (3888383293/7812500000 : ℝ) (497713061511/1000000000000 : ℝ) (501219470761/1000000000000 : ℝ) (31326216923/62500000000 : ℝ) (250603602809/500000000000 : ℝ) (250603602813/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66861/524288 : ℝ))) 3 (501219470761/1000000000000 : ℝ) (31326216923/62500000000 : ℝ) (250603602809/500000000000 : ℝ) (250603602813/500000000000 : ℝ) (501213338189/1000000000000 : ℝ) (501213338197/1000000000000 : ℝ) (501213338151/1000000000000 : ℝ) (6265166727/12500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66861/524288 : ℝ))) 4 (501213338189/1000000000000 : ℝ) (501213338197/1000000000000 : ℝ) (501213338151/1000000000000 : ℝ) (6265166727/12500000000 : ℝ) (50121333817/100000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66861/524288 : ℝ))) 5 (50121333817/100000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66861/524288 : ℝ))) 6 (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66861/524288 : ℝ))) 7 (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66861/524288 : ℝ)) hmem 8 (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66861/524288 : ℝ))) hcmem 8 (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66861/524288 : ℝ)) (496038491743/500000000000 : ℝ) (992076983489/1000000000000 : ℝ) (501213338169/1000000000000 : ℝ) (501213338179/1000000000000 : ℝ) (793591710763/1000000000000 : ℝ) (793591710783/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0788_exp_lower
  have heNumeric : (205490163357/100000000000 : ℝ)/4 ≤ Real.exp (-21314124198181/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (205490163357/100000000000 : ℝ)/4 ≤ Real.exp ((16715/131072 : ℝ)-(793591710783/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16715/131072 : ℝ) (66861/524288 : ℝ) (793591710783/1000000000000 : ℝ) (205490163357/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0789; no trusted numerical premise.
theorem cover8_leaf0789_exp_radius : (199601868223063999/200000000000000000 : ℝ) ≤ Real.exp ((-33431/2097152 : ℝ)/8) ∧ Real.exp ((-33431/2097152 : ℝ)/8) ≤ (249502335278829999/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33431/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0789_exp_lower : (14376772706607029/15625000000000000 : ℝ) ≤ Real.exp ((-85256496969411/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256496969411/128000000000000 : ℝ)/8) ≤ (920113453222849857/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256496969411/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0789_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901630733/1000000000000 : ℝ) ≤ 4*Real.exp (66861/524288 : ℝ)*Real.exp (-mu (radius 8 (33431/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901630733/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33431/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0789_exp_radius
  have hrNumeric : (492092622253/500000000000 : ℝ) ≤ Real.exp (-33431/2097152 : ℝ) ∧ Real.exp (-33431/2097152 : ℝ) ≤ (984185244507/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492092622253/500000000000 : ℝ) ≤ (radius 8 (33431/262144 : ℝ)) ∧ (radius 8 (33431/262144 : ℝ)) ≤ (984185244507/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33431/262144 : ℝ)) (492092622253/500000000000 : ℝ) (984185244507/1000000000000 : ℝ) (88571164177/500000000000 : ℝ) (4428558209/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33431/262144 : ℝ)) (492092622253/500000000000 : ℝ) (984185244507/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33431/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492092622253/500000000000 : ℝ) (984185244507/1000000000000 : ℝ) (992092622253/1000000000000 : ℝ) (496046311127/500000000000 : ℝ) (992061109259/1000000000000 : ℝ) (992061109261/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33431/262144 : ℝ)) 1 (992092622253/1000000000000 : ℝ) (496046311127/500000000000 : ℝ) (992061109259/1000000000000 : ℝ) (992061109261/1000000000000 : ℝ) (248019216439/250000000000 : ℝ) (496038432879/500000000000 : ℝ) (99207686563/100000000000 : ℝ) (992076865633/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33431/262144 : ℝ)) 2 (248019216439/250000000000 : ℝ) (496038432879/500000000000 : ℝ) (99207686563/100000000000 : ℝ) (992076865633/1000000000000 : ℝ) (992076865693/1000000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33431/262144 : ℝ)) 3 (992076865693/1000000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33431/262144 : ℝ)) 4 (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33431/262144 : ℝ)) 5 (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33431/262144 : ℝ)) 6 (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33431/262144 : ℝ)) 7 (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33431/262144 : ℝ))) (88571164177/500000000000 : ℝ) (4428558209/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33431/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88571164177/500000000000 : ℝ) (4428558209/25000000000 : ℝ) (588571164177/1000000000000 : ℝ) (29428558209/50000000000 : ℝ) (420882796457/1000000000000 : ℝ) (84176559293/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33431/262144 : ℝ))) 1 (588571164177/1000000000000 : ℝ) (29428558209/50000000000 : ℝ) (420882796457/1000000000000 : ℝ) (84176559293/200000000000 : ℝ) (504726980317/1000000000000 : ℝ) (504726980323/1000000000000 : ℝ) (124428563213/250000000000 : ℝ) (497714252859/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33431/262144 : ℝ))) 2 (504726980317/1000000000000 : ℝ) (504726980323/1000000000000 : ℝ) (124428563213/250000000000 : ℝ) (497714252859/1000000000000 : ℝ) (62652577073/125000000000 : ℝ) (501220616591/1000000000000 : ℝ) (125302087947/250000000000 : ℝ) (125302087949/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33431/262144 : ℝ))) 3 (62652577073/125000000000 : ℝ) (501220616591/1000000000000 : ℝ) (125302087947/250000000000 : ℝ) (125302087949/250000000000 : ℝ) (250607242093/500000000000 : ℝ) (250607242097/500000000000 : ℝ) (125303621037/250000000000 : ℝ) (125303621039/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33431/262144 : ℝ))) 4 (250607242093/500000000000 : ℝ) (250607242097/500000000000 : ℝ) (125303621037/250000000000 : ℝ) (125303621039/250000000000 : ℝ) (501214484167/1000000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33431/262144 : ℝ))) 5 (501214484167/1000000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33431/262144 : ℝ))) 6 (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33431/262144 : ℝ))) 7 (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33431/262144 : ℝ)) hmem 8 (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33431/262144 : ℝ))) hcmem 8 (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33431/262144 : ℝ)) (248019216423/250000000000 : ℝ) (31002402053/31250000000 : ℝ) (250607242083/500000000000 : ℝ) (20048579367/40000000000 : ℝ) (396796809747/500000000000 : ℝ) (99199202439/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0789_exp_lower
  have heNumeric : (2054901630733/1000000000000 : ℝ)/4 ≤ Real.exp (-85256496969411/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901630733/1000000000000 : ℝ)/4 ≤ Real.exp ((66861/524288 : ℝ)-(99199202439/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66861/524288 : ℝ) (33431/262144 : ℝ) (99199202439/125000000000 : ℝ) (2054901630733/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0790; no trusted numerical premise.
theorem cover8_leaf0790_exp_radius : (249502327843081077/250000000000000000 : ℝ) ≤ Real.exp ((-66863/4194304 : ℝ)/8) ∧ Real.exp ((-66863/4194304 : ℝ)/8) ≤ (998009311372324309/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66863/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0790_exp_lower : (920113453066158309/1000000000000000000 : ℝ) ≤ Real.exp ((-42628248571897/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628248571897/64000000000000 : ℝ)/8) ≤ (92011345306615831/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628248571897/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0790_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027450813967/500000000000 : ℝ) ≤ 4*Real.exp (33431/262144 : ℝ)*Real.exp (-mu (radius 8 (66863/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (1027450813967/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66863/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0790_exp_radius
  have hrNumeric : (492092504929/500000000000 : ℝ) ≤ Real.exp (-66863/4194304 : ℝ) ∧ Real.exp (-66863/4194304 : ℝ) ≤ (984185009859/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492092504929/500000000000 : ℝ) ≤ (radius 8 (66863/524288 : ℝ)) ∧ (radius 8 (66863/524288 : ℝ)) ≤ (984185009859/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66863/524288 : ℝ)) (492092504929/500000000000 : ℝ) (984185009859/1000000000000 : ℝ) (17714363203/100000000000 : ℝ) (44285908009/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66863/524288 : ℝ)) (492092504929/500000000000 : ℝ) (984185009859/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66863/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492092504929/500000000000 : ℝ) (984185009859/1000000000000 : ℝ) (992092504929/1000000000000 : ℝ) (99209250493/100000000000 : ℝ) (992060990997/1000000000000 : ℝ) (496030495499/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66863/524288 : ℝ)) 1 (992092504929/1000000000000 : ℝ) (99209250493/100000000000 : ℝ) (992060990997/1000000000000 : ℝ) (496030495499/500000000000 : ℝ) (992076747963/1000000000000 : ℝ) (248019186991/250000000000 : ℝ) (992076747837/1000000000000 : ℝ) (992076747839/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66863/524288 : ℝ)) 2 (992076747963/1000000000000 : ℝ) (248019186991/250000000000 : ℝ) (992076747837/1000000000000 : ℝ) (992076747839/1000000000000 : ℝ) (9920767479/10000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66863/524288 : ℝ)) 3 (9920767479/10000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66863/524288 : ℝ)) 4 (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66863/524288 : ℝ)) 5 (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66863/524288 : ℝ)) 6 (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66863/524288 : ℝ)) 7 (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66863/524288 : ℝ))) (17714363203/100000000000 : ℝ) (44285908009/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66863/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17714363203/100000000000 : ℝ) (44285908009/250000000000 : ℝ) (117714363203/200000000000 : ℝ) (294285908009/500000000000 : ℝ) (210442172597/500000000000 : ℝ) (210442172601/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66863/524288 : ℝ))) 1 (117714363203/200000000000 : ℝ) (294285908009/500000000000 : ℝ) (210442172597/500000000000 : ℝ) (210442172601/500000000000 : ℝ) (126182020151/250000000000 : ℝ) (50472808061/100000000000 : ℝ) (497715444187/1000000000000 : ℝ) (248857722097/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66863/524288 : ℝ))) 2 (126182020151/250000000000 : ℝ) (50472808061/100000000000 : ℝ) (497715444187/1000000000000 : ℝ) (248857722097/500000000000 : ℝ) (100244352479/200000000000 : ℝ) (250610881201/500000000000 : ℝ) (250604748973/500000000000 : ℝ) (501209497953/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66863/524288 : ℝ))) 3 (100244352479/200000000000 : ℝ) (250610881201/500000000000 : ℝ) (250604748973/500000000000 : ℝ) (501209497953/1000000000000 : ℝ) (50121563017/100000000000 : ℝ) (250607815089/500000000000 : ℝ) (125303907533/250000000000 : ℝ) (25060781507/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66863/524288 : ℝ))) 4 (50121563017/100000000000 : ℝ) (250607815089/500000000000 : ℝ) (125303907533/250000000000 : ℝ) (25060781507/50000000000 : ℝ) (501215630151/1000000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66863/524288 : ℝ))) 5 (501215630151/1000000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66863/524288 : ℝ))) 6 (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66863/524288 : ℝ))) 7 (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66863/524288 : ℝ)) hmem 8 (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66863/524288 : ℝ))) hcmem 8 (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66863/524288 : ℝ)) (992076747899/1000000000000 : ℝ) (496038373951/500000000000 : ℝ) (10024312603/20000000000 : ℝ) (501215630159/1000000000000 : ℝ) (158719105641/200000000000 : ℝ) (793595528223/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0790_exp_lower
  have heNumeric : (1027450813967/500000000000 : ℝ)/4 ≤ Real.exp (-42628248571897/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027450813967/500000000000 : ℝ)/4 ≤ Real.exp ((33431/262144 : ℝ)-(793595528223/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33431/262144 : ℝ) (66863/524288 : ℝ) (793595528223/1000000000000 : ℝ) (1027450813967/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0791; no trusted numerical premise.
theorem cover8_leaf0791_exp_radius : (249502320407332377/250000000000000000 : ℝ) ≤ Real.exp ((-4179/262144 : ℝ)/8) ∧ Real.exp ((-4179/262144 : ℝ)/8) ≤ (998009281629329509/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4179/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0791_exp_lower : (920113452911537017/1000000000000000000 : ℝ) ≤ Real.exp ((-85256497315873/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256497315873/128000000000000 : ℝ)/8) ≤ (460056726455768509/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256497315873/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0791_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901625171/1000000000000 : ℝ) ≤ 4*Real.exp (66863/524288 : ℝ)*Real.exp (-mu (radius 8 (4179/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901625171/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4179/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0791_exp_radius
  have hrNumeric : (98418477521/100000000000 : ℝ) ≤ Real.exp (-4179/262144 : ℝ) ∧ Real.exp (-4179/262144 : ℝ) ≤ (984184775211/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98418477521/100000000000 : ℝ) ≤ (radius 8 (4179/32768 : ℝ)) ∧ (radius 8 (4179/32768 : ℝ)) ≤ (984184775211/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4179/32768 : ℝ)) (98418477521/100000000000 : ℝ) (984184775211/1000000000000 : ℝ) (11071558481/62500000000 : ℝ) (88572467851/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4179/32768 : ℝ)) (98418477521/100000000000 : ℝ) (984184775211/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4179/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98418477521/100000000000 : ℝ) (984184775211/1000000000000 : ℝ) (198418477521/200000000000 : ℝ) (496046193803/500000000000 : ℝ) (496030436367/500000000000 : ℝ) (198412174547/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4179/32768 : ℝ)) 1 (198418477521/200000000000 : ℝ) (496046193803/500000000000 : ℝ) (496030436367/500000000000 : ℝ) (198412174547/200000000000 : ℝ) (992076630169/1000000000000 : ℝ) (992076630171/1000000000000 : ℝ) (248019157511/250000000000 : ℝ) (496038315023/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4179/32768 : ℝ)) 2 (992076630169/1000000000000 : ℝ) (992076630171/1000000000000 : ℝ) (248019157511/250000000000 : ℝ) (496038315023/500000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4179/32768 : ℝ)) 3 (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4179/32768 : ℝ)) 4 (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4179/32768 : ℝ)) 5 (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4179/32768 : ℝ)) 6 (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4179/32768 : ℝ)) 7 (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4179/32768 : ℝ))) (11071558481/62500000000 : ℝ) (88572467851/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4179/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11071558481/62500000000 : ℝ) (88572467851/500000000000 : ℝ) (73571558481/125000000000 : ℝ) (588572467851/1000000000000 : ℝ) (210442946957/500000000000 : ℝ) (210442946961/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4179/32768 : ℝ))) 1 (73571558481/125000000000 : ℝ) (588572467851/1000000000000 : ℝ) (210442946957/500000000000 : ℝ) (210442946961/500000000000 : ℝ) (504729180881/1000000000000 : ℝ) (504729180887/1000000000000 : ℝ) (497716635509/1000000000000 : ℝ) (124429158879/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4179/32768 : ℝ))) 2 (504729180881/1000000000000 : ℝ) (504729180887/1000000000000 : ℝ) (497716635509/1000000000000 : ℝ) (124429158879/250000000000 : ℝ) (100244581639/200000000000 : ℝ) (250611454101/500000000000 : ℝ) (125302661023/250000000000 : ℝ) (501210644099/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4179/32768 : ℝ))) 3 (100244581639/200000000000 : ℝ) (250611454101/500000000000 : ℝ) (125302661023/250000000000 : ℝ) (501210644099/1000000000000 : ℝ) (501216776143/1000000000000 : ℝ) (501216776151/1000000000000 : ℝ) (100243355221/200000000000 : ℝ) (501216776113/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4179/32768 : ℝ))) 4 (501216776143/1000000000000 : ℝ) (501216776151/1000000000000 : ℝ) (100243355221/200000000000 : ℝ) (501216776113/1000000000000 : ℝ) (125304194031/250000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4179/32768 : ℝ))) 5 (125304194031/250000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4179/32768 : ℝ))) 6 (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4179/32768 : ℝ))) 7 (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4179/32768 : ℝ)) hmem 8 (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4179/32768 : ℝ))) hcmem 8 (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4179/32768 : ℝ)) (496038315053/500000000000 : ℝ) (992076630109/1000000000000 : ℝ) (501216776123/1000000000000 : ℝ) (125304194033/250000000000 : ℝ) (793597436899/1000000000000 : ℝ) (198399359229/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0791_exp_lower
  have heNumeric : (2054901625171/1000000000000 : ℝ)/4 ≤ Real.exp (-85256497315873/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901625171/1000000000000 : ℝ)/4 ≤ Real.exp ((66863/524288 : ℝ)-(198399359229/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66863/524288 : ℝ) (4179/32768 : ℝ) (198399359229/250000000000 : ℝ) (2054901625171/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0792; no trusted numerical premise.
theorem cover8_leaf0792_exp_radius : (499004625943167797/500000000000000000 : ℝ) ≤ Real.exp ((-66865/4194304 : ℝ)/8) ∧ Real.exp ((-66865/4194304 : ℝ)/8) ≤ (199601850377267119/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66865/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0792_exp_lower : (460056726379320469/500000000000000000 : ℝ) ≤ Real.exp ((-5328531092877/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328531092877/8000000000000 : ℝ)/8) ≤ (920113452758640939/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328531092877/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0792_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901622439/1000000000000 : ℝ) ≤ 4*Real.exp (4179/32768 : ℝ)*Real.exp (-mu (radius 8 (66865/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901622439/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66865/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0792_exp_radius
  have hrNumeric : (492092270281/500000000000 : ℝ) ≤ Real.exp (-66865/4194304 : ℝ) ∧ Real.exp (-66865/4194304 : ℝ) ≤ (984184540563/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492092270281/500000000000 : ℝ) ≤ (radius 8 (66865/524288 : ℝ)) ∧ (radius 8 (66865/524288 : ℝ)) ≤ (984184540563/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66865/524288 : ℝ)) (492092270281/500000000000 : ℝ) (984184540563/1000000000000 : ℝ) (22143279919/125000000000 : ℝ) (177146239359/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66865/524288 : ℝ)) (492092270281/500000000000 : ℝ) (984184540563/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66865/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492092270281/500000000000 : ℝ) (984184540563/1000000000000 : ℝ) (992092270281/1000000000000 : ℝ) (496046135141/500000000000 : ℝ) (992060754471/1000000000000 : ℝ) (124007594309/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66865/524288 : ℝ)) 1 (992092270281/1000000000000 : ℝ) (496046135141/500000000000 : ℝ) (992060754471/1000000000000 : ℝ) (124007594309/125000000000 : ℝ) (124009564047/125000000000 : ℝ) (992076512377/1000000000000 : ℝ) (3968306049/4000000000 : ℝ) (248019128063/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66865/524288 : ℝ)) 2 (124009564047/125000000000 : ℝ) (992076512377/1000000000000 : ℝ) (3968306049/4000000000 : ℝ) (248019128063/250000000000 : ℝ) (992076512313/1000000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66865/524288 : ℝ)) 3 (992076512313/1000000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66865/524288 : ℝ)) 4 (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66865/524288 : ℝ)) 5 (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66865/524288 : ℝ)) 6 (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66865/524288 : ℝ)) 7 (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66865/524288 : ℝ))) (22143279919/125000000000 : ℝ) (177146239359/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66865/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22143279919/125000000000 : ℝ) (177146239359/1000000000000 : ℝ) (147143279919/250000000000 : ℝ) (1839290999/3125000000 : ℝ) (52610930327/125000000000 : ℝ) (3367099541/8000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66865/524288 : ℝ))) 1 (147143279919/250000000000 : ℝ) (1839290999/3125000000 : ℝ) (52610930327/125000000000 : ℝ) (3367099541/8000000000 : ℝ) (252365140573/500000000000 : ℝ) (504730281153/1000000000000 : ℝ) (248858913409/500000000000 : ℝ) (248858913413/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66865/524288 : ℝ))) 2 (252365140573/500000000000 : ℝ) (504730281153/1000000000000 : ℝ) (248858913409/500000000000 : ℝ) (248858913413/500000000000 : ℝ) (250612026991/500000000000 : ℝ) (50122405399/100000000000 : ℝ) (20048471609/40000000000 : ℝ) (250605895117/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66865/524288 : ℝ))) 3 (250612026991/500000000000 : ℝ) (50122405399/100000000000 : ℝ) (20048471609/40000000000 : ℝ) (250605895117/500000000000 : ℝ) (501217922103/1000000000000 : ℝ) (7831530033/15625000000 : ℝ) (100243584413/200000000000 : ℝ) (20048716883/40000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66865/524288 : ℝ))) 4 (501217922103/1000000000000 : ℝ) (7831530033/15625000000 : ℝ) (100243584413/200000000000 : ℝ) (20048716883/40000000000 : ℝ) (125304480521/250000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66865/524288 : ℝ))) 5 (125304480521/250000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66865/524288 : ℝ))) 6 (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66865/524288 : ℝ))) 7 (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66865/524288 : ℝ)) hmem 8 (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66865/524288 : ℝ))) hcmem 8 (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66865/524288 : ℝ)) (124009564039/125000000000 : ℝ) (198415302463/200000000000 : ℝ) (501217922083/1000000000000 : ℝ) (250608961047/500000000000 : ℝ) (793599345573/1000000000000 : ℝ) (396799672797/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0792_exp_lower
  have heNumeric : (2054901622439/1000000000000 : ℝ)/4 ≤ Real.exp (-5328531092877/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901622439/1000000000000 : ℝ)/4 ≤ Real.exp ((4179/32768 : ℝ)-(396799672797/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4179/32768 : ℝ) (66865/524288 : ℝ) (396799672797/500000000000 : ℝ) (2054901622439/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0793; no trusted numerical premise.
theorem cover8_leaf0793_exp_radius : (998009222143342567/1000000000000000000 : ℝ) ≤ Real.exp ((-33433/2097152 : ℝ)/8) ∧ Real.exp ((-33433/2097152 : ℝ)/8) ≤ (124751152767917821/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33433/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0793_exp_lower : (920113452608620213/1000000000000000000 : ℝ) ≤ Real.exp ((-85256497652991/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256497652991/128000000000000 : ℝ)/8) ≤ (460056726304310107/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256497652991/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0793_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901619759/1000000000000 : ℝ) ≤ 4*Real.exp (66865/524288 : ℝ)*Real.exp (-mu (radius 8 (33433/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901619759/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33433/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0793_exp_radius
  have hrNumeric : (492092152957/500000000000 : ℝ) ≤ Real.exp (-33433/2097152 : ℝ) ∧ Real.exp (-33433/2097152 : ℝ) ≤ (196836861183/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492092152957/500000000000 : ℝ) ≤ (radius 8 (33433/262144 : ℝ)) ∧ (radius 8 (33433/262144 : ℝ)) ≤ (196836861183/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33433/262144 : ℝ)) (492092152957/500000000000 : ℝ) (196836861183/200000000000 : ℝ) (177147542999/1000000000000 : ℝ) (35429508601/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33433/262144 : ℝ)) (492092152957/500000000000 : ℝ) (196836861183/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33433/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492092152957/500000000000 : ℝ) (196836861183/200000000000 : ℝ) (992092152957/1000000000000 : ℝ) (496046076479/500000000000 : ℝ) (62003789763/62500000000 : ℝ) (992060636209/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33433/262144 : ℝ)) 1 (992092152957/1000000000000 : ℝ) (496046076479/500000000000 : ℝ) (62003789763/62500000000 : ℝ) (992060636209/1000000000000 : ℝ) (496038197291/500000000000 : ℝ) (124009549323/125000000000 : ℝ) (992076394457/1000000000000 : ℝ) (992076394459/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33433/262144 : ℝ)) 2 (496038197291/500000000000 : ℝ) (124009549323/125000000000 : ℝ) (992076394457/1000000000000 : ℝ) (992076394459/1000000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33433/262144 : ℝ)) 3 (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33433/262144 : ℝ)) 4 (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33433/262144 : ℝ)) 5 (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33433/262144 : ℝ)) 6 (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33433/262144 : ℝ)) 7 (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33433/262144 : ℝ))) (177147542999/1000000000000 : ℝ) (35429508601/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33433/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177147542999/1000000000000 : ℝ) (35429508601/200000000000 : ℝ) (588573771499/1000000000000 : ℝ) (588573771503/1000000000000 : ℝ) (420888991301/1000000000000 : ℝ) (420888991309/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33433/262144 : ℝ))) 1 (588573771499/1000000000000 : ℝ) (588573771503/1000000000000 : ℝ) (420888991301/1000000000000 : ℝ) (420888991309/1000000000000 : ℝ) (2523656907/5000000000 : ℝ) (252365690703/500000000000 : ℝ) (248859509057/500000000000 : ℝ) (497719018121/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33433/262144 : ℝ))) 2 (2523656907/5000000000 : ℝ) (252365690703/500000000000 : ℝ) (248859509057/500000000000 : ℝ) (497719018121/1000000000000 : ℝ) (501225199757/1000000000000 : ℝ) (125306299941/250000000000 : ℝ) (501212936347/1000000000000 : ℝ) (250606468177/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33433/262144 : ℝ))) 3 (501225199757/1000000000000 : ℝ) (125306299941/250000000000 : ℝ) (501212936347/1000000000000 : ℝ) (250606468177/500000000000 : ℝ) (125304767013/250000000000 : ℝ) (501219068059/1000000000000 : ℝ) (250609534007/500000000000 : ℝ) (250609534011/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33433/262144 : ℝ))) 4 (125304767013/250000000000 : ℝ) (501219068059/1000000000000 : ℝ) (250609534007/500000000000 : ℝ) (250609534011/500000000000 : ℝ) (501219068033/1000000000000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33433/262144 : ℝ))) 5 (501219068033/1000000000000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33433/262144 : ℝ))) 6 (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33433/262144 : ℝ))) 7 (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33433/262144 : ℝ)) hmem 8 (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33433/262144 : ℝ))) hcmem 8 (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33433/262144 : ℝ)) (992076394519/1000000000000 : ℝ) (496038197261/500000000000 : ℝ) (3915773969/7812500000 : ℝ) (501219068041/1000000000000 : ℝ) (793601254229/1000000000000 : ℝ) (793601254247/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0793_exp_lower
  have heNumeric : (2054901619759/1000000000000 : ℝ)/4 ≤ Real.exp (-85256497652991/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901619759/1000000000000 : ℝ)/4 ≤ Real.exp ((66865/524288 : ℝ)-(793601254247/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66865/524288 : ℝ) (33433/262144 : ℝ) (793601254247/1000000000000 : ℝ) (2054901619759/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0794; no trusted numerical premise.
theorem cover8_leaf0794_exp_radius : (499004596200175213/500000000000000000 : ℝ) ≤ Real.exp ((-66867/4194304 : ℝ)/8) ∧ Real.exp ((-66867/4194304 : ℝ)/8) ≤ (998009192400350427/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66867/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0794_exp_lower : (230028363115109929/250000000000000000 : ℝ) ≤ Real.exp ((-42628248908951/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628248908951/64000000000000 : ℝ)/8) ≤ (920113452460439717/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628248908951/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0794_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256862702139/125000000000 : ℝ) ≤ 4*Real.exp (33433/262144 : ℝ)*Real.exp (-mu (radius 8 (66867/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (256862702139/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66867/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0794_exp_radius
  have hrNumeric : (492092035633/500000000000 : ℝ) ≤ Real.exp (-66867/4194304 : ℝ) ∧ Real.exp (-66867/4194304 : ℝ) ≤ (984184071267/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492092035633/500000000000 : ℝ) ≤ (radius 8 (66867/524288 : ℝ)) ∧ (radius 8 (66867/524288 : ℝ)) ≤ (984184071267/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66867/524288 : ℝ)) (492092035633/500000000000 : ℝ) (984184071267/1000000000000 : ℝ) (35429769327/200000000000 : ℝ) (88574423321/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66867/524288 : ℝ)) (492092035633/500000000000 : ℝ) (984184071267/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66867/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492092035633/500000000000 : ℝ) (984184071267/1000000000000 : ℝ) (992092035633/1000000000000 : ℝ) (496046017817/500000000000 : ℝ) (198412103589/200000000000 : ℝ) (496030258973/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66867/524288 : ℝ)) 1 (992092035633/1000000000000 : ℝ) (496046017817/500000000000 : ℝ) (198412103589/200000000000 : ℝ) (496030258973/500000000000 : ℝ) (992076276789/1000000000000 : ℝ) (99207627679/100000000000 : ℝ) (992076276663/1000000000000 : ℝ) (198415255333/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66867/524288 : ℝ)) 2 (992076276789/1000000000000 : ℝ) (99207627679/100000000000 : ℝ) (992076276663/1000000000000 : ℝ) (198415255333/200000000000 : ℝ) (496038138363/500000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66867/524288 : ℝ)) 3 (496038138363/500000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66867/524288 : ℝ)) 4 (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66867/524288 : ℝ)) 5 (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66867/524288 : ℝ)) 6 (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66867/524288 : ℝ)) 7 (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66867/524288 : ℝ))) (35429769327/200000000000 : ℝ) (88574423321/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66867/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35429769327/200000000000 : ℝ) (88574423321/500000000000 : ℝ) (588574423317/1000000000000 : ℝ) (588574423321/1000000000000 : ℝ) (6576414687/15625000000 : ℝ) (420890539977/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66867/524288 : ℝ))) 1 (588574423317/1000000000000 : ℝ) (588574423321/1000000000000 : ℝ) (6576414687/15625000000 : ℝ) (420890539977/1000000000000 : ℝ) (252366240821/500000000000 : ℝ) (504732481649/1000000000000 : ℝ) (124430052349/250000000000 : ℝ) (124430052351/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66867/524288 : ℝ))) 2 (252366240821/500000000000 : ℝ) (504732481649/1000000000000 : ℝ) (124430052349/250000000000 : ℝ) (124430052351/250000000000 : ℝ) (501226345519/1000000000000 : ℝ) (501226345527/1000000000000 : ℝ) (100242816491/200000000000 : ℝ) (15662940077/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66867/524288 : ℝ))) 3 (501226345519/1000000000000 : ℝ) (501226345527/1000000000000 : ℝ) (100242816491/200000000000 : ℝ) (15662940077/31250000000 : ℝ) (501220213987/1000000000000 : ℝ) (125305053499/250000000000 : ℝ) (501220213949/1000000000000 : ℝ) (250610106979/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66867/524288 : ℝ))) 4 (501220213987/1000000000000 : ℝ) (125305053499/250000000000 : ℝ) (501220213949/1000000000000 : ℝ) (250610106979/500000000000 : ℝ) (31326263373/62500000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66867/524288 : ℝ))) 5 (31326263373/62500000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66867/524288 : ℝ))) 6 (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66867/524288 : ℝ))) 7 (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66867/524288 : ℝ)) hmem 8 (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66867/524288 : ℝ))) hcmem 8 (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66867/524288 : ℝ)) (39683051069/40000000000 : ℝ) (124009534591/125000000000 : ℝ) (501220213967/1000000000000 : ℝ) (501220213977/1000000000000 : ℝ) (158720632573/200000000000 : ℝ) (198400790721/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0794_exp_lower
  have heNumeric : (256862702139/125000000000 : ℝ)/4 ≤ Real.exp (-42628248908951/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256862702139/125000000000 : ℝ)/4 ≤ Real.exp ((33433/262144 : ℝ)-(198400790721/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33433/262144 : ℝ) (66867/524288 : ℝ) (198400790721/250000000000 : ℝ) (256862702139/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0795; no trusted numerical premise.
theorem cover8_leaf0795_exp_radius : (998009162657359171/1000000000000000000 : ℝ) ≤ Real.exp ((-16717/1048576 : ℝ)/8) ∧ Real.exp ((-16717/1048576 : ℝ)/8) ≤ (249502290664339793/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16717/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0795_exp_lower : (460056726157279751/500000000000000000 : ℝ) ≤ Real.exp ((-85256497980253/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256497980253/128000000000000 : ℝ)/8) ≤ (920113452314559503/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256497980253/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0795_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410980322901/200000000000 : ℝ) ≤ 4*Real.exp (66867/524288 : ℝ)*Real.exp (-mu (radius 8 (16717/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410980322901/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16717/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0795_exp_radius
  have hrNumeric : (492091918309/500000000000 : ℝ) ≤ Real.exp (-16717/1048576 : ℝ) ∧ Real.exp (-16717/1048576 : ℝ) ≤ (984183836619/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (492091918309/500000000000 : ℝ) ≤ (radius 8 (16717/131072 : ℝ)) ∧ (radius 8 (16717/131072 : ℝ)) ≤ (984183836619/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16717/131072 : ℝ)) (492091918309/500000000000 : ℝ) (984183836619/1000000000000 : ℝ) (88575075131/500000000000 : ℝ) (44287537567/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16717/131072 : ℝ)) (492091918309/500000000000 : ℝ) (984183836619/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16717/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (492091918309/500000000000 : ℝ) (984183836619/1000000000000 : ℝ) (992091918309/1000000000000 : ℝ) (99209191831/100000000000 : ℝ) (496030199841/500000000000 : ℝ) (992060399683/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16717/131072 : ℝ)) 1 (992091918309/1000000000000 : ℝ) (99209191831/100000000000 : ℝ) (496030199841/500000000000 : ℝ) (992060399683/1000000000000 : ℝ) (198415231799/200000000000 : ℝ) (992076158997/1000000000000 : ℝ) (99207615887/100000000000 : ℝ) (124009519859/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16717/131072 : ℝ)) 2 (198415231799/200000000000 : ℝ) (992076158997/1000000000000 : ℝ) (99207615887/100000000000 : ℝ) (124009519859/125000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16717/131072 : ℝ)) 3 (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16717/131072 : ℝ)) 4 (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16717/131072 : ℝ)) 5 (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16717/131072 : ℝ)) 6 (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16717/131072 : ℝ)) 7 (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16717/131072 : ℝ))) (88575075131/500000000000 : ℝ) (44287537567/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16717/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88575075131/500000000000 : ℝ) (44287537567/250000000000 : ℝ) (588575075131/1000000000000 : ℝ) (294287537567/500000000000 : ℝ) (210446044309/500000000000 : ℝ) (420892088627/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16717/131072 : ℝ))) 1 (588575075131/1000000000000 : ℝ) (294287537567/500000000000 : ℝ) (210446044309/500000000000 : ℝ) (420892088627/1000000000000 : ℝ) (252366790937/500000000000 : ℝ) (504733581881/1000000000000 : ℝ) (99544280133/200000000000 : ℝ) (497721400673/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16717/131072 : ℝ))) 2 (252366790937/500000000000 : ℝ) (504733581881/1000000000000 : ℝ) (99544280133/200000000000 : ℝ) (497721400673/1000000000000 : ℝ) (501227491269/1000000000000 : ℝ) (501227491277/1000000000000 : ℝ) (62651903569/125000000000 : ℝ) (501215228561/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16717/131072 : ℝ))) 3 (501227491269/1000000000000 : ℝ) (501227491277/1000000000000 : ℝ) (62651903569/125000000000 : ℝ) (501215228561/1000000000000 : ℝ) (50122135991/100000000000 : ℝ) (501221359919/1000000000000 : ℝ) (1957895937/3906250000 : ℝ) (250610679941/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16717/131072 : ℝ))) 4 (50122135991/100000000000 : ℝ) (501221359919/1000000000000 : ℝ) (1957895937/3906250000 : ℝ) (250610679941/500000000000 : ℝ) (501221359891/1000000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16717/131072 : ℝ))) 5 (501221359891/1000000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16717/131072 : ℝ))) 6 (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16717/131072 : ℝ))) 7 (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16717/131072 : ℝ)) hmem 8 (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16717/131072 : ℝ))) hcmem 8 (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16717/131072 : ℝ)) (248019039733/250000000000 : ℝ) (198415231787/200000000000 : ℝ) (50122135989/100000000000 : ℝ) (501221359901/1000000000000 : ℝ) (793605071481/1000000000000 : ℝ) (793605071501/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0795_exp_lower
  have heNumeric : (410980322901/200000000000 : ℝ)/4 ≤ Real.exp (-85256497980253/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410980322901/200000000000 : ℝ)/4 ≤ Real.exp ((66867/524288 : ℝ)-(793605071501/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66867/524288 : ℝ) (16717/131072 : ℝ) (793605071501/1000000000000 : ℝ) (410980322901/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0796; no trusted numerical premise.
theorem cover8_leaf0796_exp_radius : (998009132914368803/1000000000000000000 : ℝ) ≤ Real.exp ((-66869/4194304 : ℝ)/8) ∧ Real.exp ((-66869/4194304 : ℝ)/8) ≤ (249502283228592201/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66869/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0796_exp_lower : (920113452171669657/1000000000000000000 : ℝ) ≤ Real.exp ((-21314124534819/32000000000000 : ℝ)/8) ∧ Real.exp ((-21314124534819/32000000000000 : ℝ)/8) ≤ (460056726085834829/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21314124534819/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0796_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128431350747/62500000000 : ℝ) ≤ 4*Real.exp (16717/131072 : ℝ)*Real.exp (-mu (radius 8 (66869/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (128431350747/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66869/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0796_exp_radius
  have hrNumeric : (984183601971/1000000000000 : ℝ) ≤ Real.exp (-66869/4194304 : ℝ) ∧ Real.exp (-66869/4194304 : ℝ) ≤ (246045900493/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984183601971/1000000000000 : ℝ) ≤ (radius 8 (66869/524288 : ℝ)) ∧ (radius 8 (66869/524288 : ℝ)) ≤ (246045900493/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66869/524288 : ℝ)) (984183601971/1000000000000 : ℝ) (246045900493/250000000000 : ℝ) (177151453873/1000000000000 : ℝ) (177151453879/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66869/524288 : ℝ)) (984183601971/1000000000000 : ℝ) (246045900493/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66869/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984183601971/1000000000000 : ℝ) (246045900493/250000000000 : ℝ) (198418360197/200000000000 : ℝ) (496045900493/500000000000 : ℝ) (992060281419/1000000000000 : ℝ) (992060281421/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66869/524288 : ℝ)) 1 (198418360197/200000000000 : ℝ) (496045900493/500000000000 : ℝ) (992060281419/1000000000000 : ℝ) (992060281421/1000000000000 : ℝ) (496038020601/500000000000 : ℝ) (248019010301/250000000000 : ℝ) (248019010269/250000000000 : ℝ) (992076041079/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66869/524288 : ℝ)) 2 (496038020601/500000000000 : ℝ) (248019010301/250000000000 : ℝ) (248019010269/250000000000 : ℝ) (992076041079/1000000000000 : ℝ) (992076041139/1000000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66869/524288 : ℝ)) 3 (992076041139/1000000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66869/524288 : ℝ)) 4 (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66869/524288 : ℝ)) 5 (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66869/524288 : ℝ)) 6 (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66869/524288 : ℝ)) 7 (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66869/524288 : ℝ))) (177151453873/1000000000000 : ℝ) (177151453879/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66869/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177151453873/1000000000000 : ℝ) (177151453879/1000000000000 : ℝ) (73571965867/125000000000 : ℝ) (29428786347/50000000000 : ℝ) (105223409311/250000000000 : ℝ) (105223409313/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66869/524288 : ℝ))) 1 (73571965867/125000000000 : ℝ) (29428786347/50000000000 : ℝ) (105223409311/250000000000 : ℝ) (105223409313/250000000000 : ℝ) (50473468209/100000000000 : ℝ) (31545917631/62500000000 : ℝ) (124430647979/250000000000 : ℝ) (497722591923/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66869/524288 : ℝ))) 2 (50473468209/100000000000 : ℝ) (31545917631/62500000000 : ℝ) (124430647979/250000000000 : ℝ) (497722591923/1000000000000 : ℝ) (501228637003/1000000000000 : ℝ) (50122863701/100000000000 : ℝ) (62652046829/125000000000 : ℝ) (501216374639/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66869/524288 : ℝ))) 3 (501228637003/1000000000000 : ℝ) (50122863701/100000000000 : ℝ) (62652046829/125000000000 : ℝ) (501216374639/1000000000000 : ℝ) (501222505817/1000000000000 : ℝ) (20048900233/40000000000 : ℝ) (25061125289/50000000000 : ℝ) (125305626447/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66869/524288 : ℝ))) 4 (501222505817/1000000000000 : ℝ) (20048900233/40000000000 : ℝ) (25061125289/50000000000 : ℝ) (125305626447/250000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66869/524288 : ℝ))) 5 (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66869/524288 : ℝ))) 6 (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66869/524288 : ℝ))) 7 (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66869/524288 : ℝ)) hmem 8 (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66869/524288 : ℝ))) hcmem 8 (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66869/524288 : ℝ)) (496038020569/500000000000 : ℝ) (496038020571/500000000000 : ℝ) (250611252899/500000000000 : ℝ) (501222505807/1000000000000 : ℝ) (793606980073/1000000000000 : ℝ) (198401745023/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0796_exp_lower
  have heNumeric : (128431350747/62500000000 : ℝ)/4 ≤ Real.exp (-21314124534819/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128431350747/62500000000 : ℝ)/4 ≤ Real.exp ((16717/131072 : ℝ)-(198401745023/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16717/131072 : ℝ) (66869/524288 : ℝ) (198401745023/250000000000 : ℝ) (128431350747/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0797; no trusted numerical premise.
theorem cover8_leaf0797_exp_radius : (998009103171379321/1000000000000000000 : ℝ) ≤ Real.exp ((-33435/2097152 : ℝ)/8) ∧ Real.exp ((-33435/2097152 : ℝ)/8) ≤ (499004551585689661/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33435/2097152 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0797_exp_lower : (92011345203039001/100000000000000000 : ℝ) ≤ Real.exp ((-85256498296507/128000000000000 : ℝ)/8) ∧ Real.exp ((-85256498296507/128000000000000 : ℝ)/8) ≤ (920113452030390011/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-85256498296507/128000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0797_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513725402357/250000000000 : ℝ) ≤ 4*Real.exp (66869/524288 : ℝ)*Real.exp (-mu (radius 8 (33435/262144 : ℝ))) ∧ (20549/10000 : ℝ) < (513725402357/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (33435/262144 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0797_exp_radius
  have hrNumeric : (984183367323/1000000000000 : ℝ) ≤ Real.exp (-33435/2097152 : ℝ) ∧ Real.exp (-33435/2097152 : ℝ) ≤ (246045841831/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (984183367323/1000000000000 : ℝ) ≤ (radius 8 (33435/262144 : ℝ)) ∧ (radius 8 (33435/262144 : ℝ)) ≤ (246045841831/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (33435/262144 : ℝ)) (984183367323/1000000000000 : ℝ) (246045841831/250000000000 : ℝ) (4428818937/25000000000 : ℝ) (88576378743/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (33435/262144 : ℝ)) (984183367323/1000000000000 : ℝ) (246045841831/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (33435/262144 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (984183367323/1000000000000 : ℝ) (246045841831/250000000000 : ℝ) (992091683661/1000000000000 : ℝ) (496045841831/500000000000 : ℝ) (248015040789/250000000000 : ℝ) (496030081579/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (33435/262144 : ℝ)) 1 (992091683661/1000000000000 : ℝ) (496045841831/500000000000 : ℝ) (248015040789/250000000000 : ℝ) (496030081579/500000000000 : ℝ) (62004745213/62500000000 : ℝ) (99207592341/100000000000 : ℝ) (992075923283/1000000000000 : ℝ) (198415184657/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (33435/262144 : ℝ)) 2 (62004745213/62500000000 : ℝ) (99207592341/100000000000 : ℝ) (992075923283/1000000000000 : ℝ) (198415184657/200000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (33435/262144 : ℝ)) 3 (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (33435/262144 : ℝ)) 4 (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (33435/262144 : ℝ)) 5 (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (33435/262144 : ℝ)) 6 (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (33435/262144 : ℝ)) 7 (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (33435/262144 : ℝ))) (4428818937/25000000000 : ℝ) (88576378743/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (33435/262144 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4428818937/25000000000 : ℝ) (88576378743/500000000000 : ℝ) (29428818937/50000000000 : ℝ) (588576378743/1000000000000 : ℝ) (420895185859/1000000000000 : ℝ) (420895185867/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (33435/262144 : ℝ))) 1 (29428818937/50000000000 : ℝ) (588576378743/1000000000000 : ℝ) (420895185859/1000000000000 : ℝ) (420895185867/1000000000000 : ℝ) (504735782299/1000000000000 : ℝ) (100947156461/200000000000 : ℝ) (248861891579/500000000000 : ℝ) (99544756633/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (33435/262144 : ℝ))) 2 (504735782299/1000000000000 : ℝ) (100947156461/200000000000 : ℝ) (248861891579/500000000000 : ℝ) (99544756633/200000000000 : ℝ) (62653722841/125000000000 : ℝ) (100245956547/200000000000 : ℝ) (7831523761/15625000000 : ℝ) (501217520711/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (33435/262144 : ℝ))) 3 (62653722841/125000000000 : ℝ) (100245956547/200000000000 : ℝ) (7831523761/15625000000 : ℝ) (501217520711/1000000000000 : ℝ) (125305912929/250000000000 : ℝ) (501223651723/1000000000000 : ℝ) (250611825839/500000000000 : ℝ) (250611825843/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (33435/262144 : ℝ))) 4 (125305912929/250000000000 : ℝ) (501223651723/1000000000000 : ℝ) (250611825839/500000000000 : ℝ) (250611825843/500000000000 : ℝ) (501223651697/1000000000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (33435/262144 : ℝ))) 5 (501223651697/1000000000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (33435/262144 : ℝ))) 6 (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (33435/262144 : ℝ))) 7 (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (33435/262144 : ℝ)) hmem 8 (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (33435/262144 : ℝ))) hcmem 8 (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (33435/262144 : ℝ)) (198415184669/200000000000 : ℝ) (248018980837/250000000000 : ℝ) (31326478231/62500000000 : ℝ) (100244730341/200000000000 : ℝ) (198402222163/250000000000 : ℝ) (793608888669/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0797_exp_lower
  have heNumeric : (513725402357/250000000000 : ℝ)/4 ≤ Real.exp (-85256498296507/128000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513725402357/250000000000 : ℝ)/4 ≤ Real.exp ((66869/524288 : ℝ)-(793608888669/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66869/524288 : ℝ) (33435/262144 : ℝ) (793608888669/1000000000000 : ℝ) (513725402357/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0798; no trusted numerical premise.
theorem cover8_leaf0798_exp_radius : (499004536714195363/500000000000000000 : ℝ) ≤ Real.exp ((-66871/4194304 : ℝ)/8) ∧ Real.exp ((-66871/4194304 : ℝ)/8) ≤ (998009073428390727/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66871/4194304 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0798_exp_lower : (920113451891755689/1000000000000000000 : ℝ) ≤ Real.exp ((-42628249225397/64000000000000 : ℝ)/8) ∧ Real.exp ((-42628249225397/64000000000000 : ℝ)/8) ≤ (92011345189175569/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-42628249225397/64000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0798_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901606951/1000000000000 : ℝ) ≤ 4*Real.exp (33435/262144 : ℝ)*Real.exp (-mu (radius 8 (66871/524288 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901606951/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (66871/524288 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0798_exp_radius
  have hrNumeric : (246045783169/250000000000 : ℝ) ≤ Real.exp (-66871/4194304 : ℝ) ∧ Real.exp (-66871/4194304 : ℝ) ≤ (984183132677/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246045783169/250000000000 : ℝ) ≤ (radius 8 (66871/524288 : ℝ)) ∧ (radius 8 (66871/524288 : ℝ)) ≤ (984183132677/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (66871/524288 : ℝ)) (246045783169/250000000000 : ℝ) (984183132677/1000000000000 : ℝ) (177154061071/1000000000000 : ℝ) (177154061077/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (66871/524288 : ℝ)) (246045783169/250000000000 : ℝ) (984183132677/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (66871/524288 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246045783169/250000000000 : ℝ) (984183132677/1000000000000 : ℝ) (496045783169/500000000000 : ℝ) (992091566339/1000000000000 : ℝ) (496030022447/500000000000 : ℝ) (198412008979/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (66871/524288 : ℝ)) 1 (496045783169/500000000000 : ℝ) (992091566339/1000000000000 : ℝ) (496030022447/500000000000 : ℝ) (198412008979/200000000000 : ℝ) (62004737851/62500000000 : ℝ) (992075805617/1000000000000 : ℝ) (99207580549/100000000000 : ℝ) (248018951373/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (66871/524288 : ℝ)) 2 (62004737851/62500000000 : ℝ) (992075805617/1000000000000 : ℝ) (99207580549/100000000000 : ℝ) (248018951373/250000000000 : ℝ) (992075805553/1000000000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (66871/524288 : ℝ)) 3 (992075805553/1000000000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (66871/524288 : ℝ)) 4 (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (66871/524288 : ℝ)) 5 (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (66871/524288 : ℝ)) 6 (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (66871/524288 : ℝ)) 7 (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (66871/524288 : ℝ))) (177154061071/1000000000000 : ℝ) (177154061077/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (66871/524288 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (177154061071/1000000000000 : ℝ) (177154061077/1000000000000 : ℝ) (117715406107/200000000000 : ℝ) (588577030539/1000000000000 : ℝ) (8417934689/20000000000 : ℝ) (210448367229/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (66871/524288 : ℝ))) 1 (117715406107/200000000000 : ℝ) (588577030539/1000000000000 : ℝ) (8417934689/20000000000 : ℝ) (210448367229/500000000000 : ℝ) (126184220623/250000000000 : ℝ) (504736882499/1000000000000 : ℝ) (248862487191/500000000000 : ℝ) (49772497439/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (66871/524288 : ℝ))) 2 (126184220623/250000000000 : ℝ) (504736882499/1000000000000 : ℝ) (248862487191/500000000000 : ℝ) (49772497439/100000000000 : ℝ) (501230928437/1000000000000 : ℝ) (100246185689/200000000000 : ℝ) (501218666759/1000000000000 : ℝ) (501218666767/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (66871/524288 : ℝ))) 3 (501230928437/1000000000000 : ℝ) (100246185689/200000000000 : ℝ) (501218666759/1000000000000 : ℝ) (501218666767/1000000000000 : ℝ) (250612398799/500000000000 : ℝ) (250612398803/500000000000 : ℝ) (12530619939/25000000000 : ℝ) (501224797569/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (66871/524288 : ℝ))) 4 (250612398799/500000000000 : ℝ) (250612398803/500000000000 : ℝ) (12530619939/25000000000 : ℝ) (501224797569/1000000000000 : ℝ) (501224797579/1000000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (66871/524288 : ℝ))) 5 (501224797579/1000000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (66871/524288 : ℝ))) 6 (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (66871/524288 : ℝ))) 7 (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (66871/524288 : ℝ)) hmem 8 (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (66871/524288 : ℝ))) hcmem 8 (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (66871/524288 : ℝ)) (62004737847/62500000000 : ℝ) (198415161111/200000000000 : ℝ) (250612398789/500000000000 : ℝ) (125306199397/250000000000 : ℝ) (198402699301/250000000000 : ℝ) (793610797223/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0798_exp_lower
  have heNumeric : (2054901606951/1000000000000 : ℝ)/4 ≤ Real.exp (-42628249225397/64000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901606951/1000000000000 : ℝ)/4 ≤ Real.exp ((33435/262144 : ℝ)-(793610797223/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (33435/262144 : ℝ) (66871/524288 : ℝ) (793610797223/1000000000000 : ℝ) (2054901606951/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf0799; no trusted numerical premise.
theorem cover8_leaf0799_exp_radius : (998009043685403017/1000000000000000000 : ℝ) ≤ Real.exp ((-8359/524288 : ℝ)/8) ∧ Real.exp ((-8359/524288 : ℝ)/8) ≤ (499004521842701509/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8359/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0799_exp_lower : (920113451754501539/1000000000000000000 : ℝ) ≤ Real.exp ((-17051299720709/25600000000000 : ℝ)/8) ∧ Real.exp ((-17051299720709/25600000000000 : ℝ)/8) ≤ (46005672587725077/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17051299720709/25600000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf0799_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054901604499/1000000000000 : ℝ) ≤ 4*Real.exp (66871/524288 : ℝ)*Real.exp (-mu (radius 8 (8359/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054901604499/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8359/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0799_exp_radius
  have hrNumeric : (246045724507/250000000000 : ℝ) ≤ Real.exp (-8359/524288 : ℝ) ∧ Real.exp (-8359/524288 : ℝ) ≤ (984182898029/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (246045724507/250000000000 : ℝ) ≤ (radius 8 (8359/65536 : ℝ)) ∧ (radius 8 (8359/65536 : ℝ)) ≤ (984182898029/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8359/65536 : ℝ)) (246045724507/250000000000 : ℝ) (984182898029/1000000000000 : ℝ) (88577682329/500000000000 : ℝ) (22144420583/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8359/65536 : ℝ)) (246045724507/250000000000 : ℝ) (984182898029/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8359/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (246045724507/250000000000 : ℝ) (984182898029/1000000000000 : ℝ) (496045724507/500000000000 : ℝ) (198418289803/200000000000 : ℝ) (992059926631/1000000000000 : ℝ) (124007490829/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8359/65536 : ℝ)) 1 (496045724507/500000000000 : ℝ) (198418289803/200000000000 : ℝ) (992059926631/1000000000000 : ℝ) (124007490829/125000000000 : ℝ) (496037843911/500000000000 : ℝ) (62004730489/62500000000 : ℝ) (992075687697/1000000000000 : ℝ) (992075687699/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8359/65536 : ℝ)) 2 (496037843911/500000000000 : ℝ) (62004730489/62500000000 : ℝ) (992075687697/1000000000000 : ℝ) (992075687699/1000000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8359/65536 : ℝ)) 3 (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8359/65536 : ℝ)) 4 (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8359/65536 : ℝ)) 5 (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8359/65536 : ℝ)) 6 (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8359/65536 : ℝ)) 7 (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8359/65536 : ℝ))) (88577682329/500000000000 : ℝ) (22144420583/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8359/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (88577682329/500000000000 : ℝ) (22144420583/125000000000 : ℝ) (588577682329/1000000000000 : ℝ) (147144420583/250000000000 : ℝ) (42089828303/100000000000 : ℝ) (210449141519/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8359/65536 : ℝ))) 1 (588577682329/1000000000000 : ℝ) (147144420583/250000000000 : ℝ) (42089828303/100000000000 : ℝ) (210449141519/500000000000 : ℝ) (504737982679/1000000000000 : ℝ) (100947596537/200000000000 : ℝ) (497726165599/1000000000000 : ℝ) (248863082803/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8359/65536 : ℝ))) 2 (504737982679/1000000000000 : ℝ) (100947596537/200000000000 : ℝ) (497726165599/1000000000000 : ℝ) (248863082803/500000000000 : ℝ) (501232074139/1000000000000 : ℝ) (250616037073/500000000000 : ℝ) (501219812807/1000000000000 : ℝ) (100243962563/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8359/65536 : ℝ))) 3 (501232074139/1000000000000 : ℝ) (250616037073/500000000000 : ℝ) (501219812807/1000000000000 : ℝ) (100243962563/200000000000 : ℝ) (501225943473/1000000000000 : ℝ) (501225943481/1000000000000 : ℝ) (100245188687/200000000000 : ℝ) (125306485861/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8359/65536 : ℝ))) 4 (501225943473/1000000000000 : ℝ) (501225943481/1000000000000 : ℝ) (100245188687/200000000000 : ℝ) (125306485861/250000000000 : ℝ) (250612971727/500000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8359/65536 : ℝ))) 5 (250612971727/500000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8359/65536 : ℝ))) 6 (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8359/65536 : ℝ))) 7 (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8359/65536 : ℝ)) hmem 8 (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8359/65536 : ℝ))) hcmem 8 (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8359/65536 : ℝ)) (992075687759/1000000000000 : ℝ) (496037843881/500000000000 : ℝ) (501225943453/1000000000000 : ℝ) (501225943463/1000000000000 : ℝ) (396806352873/500000000000 : ℝ) (158722541153/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf0799_exp_lower
  have heNumeric : (2054901604499/1000000000000 : ℝ)/4 ≤ Real.exp (-17051299720709/25600000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054901604499/1000000000000 : ℝ)/4 ≤ Real.exp ((66871/524288 : ℝ)-(158722541153/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (66871/524288 : ℝ) (8359/65536 : ℝ) (158722541153/200000000000 : ℝ) (2054901604499/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf0775_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0775_certificate
#check SmaleRate.Proofs.cover8_leaf0776_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0776_certificate
#check SmaleRate.Proofs.cover8_leaf0777_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0777_certificate
#check SmaleRate.Proofs.cover8_leaf0778_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0778_certificate
#check SmaleRate.Proofs.cover8_leaf0779_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0779_certificate
#check SmaleRate.Proofs.cover8_leaf0780_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0780_certificate
#check SmaleRate.Proofs.cover8_leaf0781_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0781_certificate
#check SmaleRate.Proofs.cover8_leaf0782_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0782_certificate
#check SmaleRate.Proofs.cover8_leaf0783_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0783_certificate
#check SmaleRate.Proofs.cover8_leaf0784_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0784_certificate
#check SmaleRate.Proofs.cover8_leaf0785_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0785_certificate
#check SmaleRate.Proofs.cover8_leaf0786_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0786_certificate
#check SmaleRate.Proofs.cover8_leaf0787_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0787_certificate
#check SmaleRate.Proofs.cover8_leaf0788_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0788_certificate
#check SmaleRate.Proofs.cover8_leaf0789_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0789_certificate
#check SmaleRate.Proofs.cover8_leaf0790_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0790_certificate
#check SmaleRate.Proofs.cover8_leaf0791_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0791_certificate
#check SmaleRate.Proofs.cover8_leaf0792_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0792_certificate
#check SmaleRate.Proofs.cover8_leaf0793_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0793_certificate
#check SmaleRate.Proofs.cover8_leaf0794_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0794_certificate
#check SmaleRate.Proofs.cover8_leaf0795_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0795_certificate
#check SmaleRate.Proofs.cover8_leaf0796_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0796_certificate
#check SmaleRate.Proofs.cover8_leaf0797_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0797_certificate
#check SmaleRate.Proofs.cover8_leaf0798_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0798_certificate
#check SmaleRate.Proofs.cover8_leaf0799_certificate
#print axioms SmaleRate.Proofs.cover8_leaf0799_certificate
