/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover7_leaf0075; no trusted numerical premise.
theorem cover7_leaf0075_exp_radius : (997685526423379181/1000000000000000000 : ℝ) ≤ Real.exp ((-1063/57344 : ℝ)/8) ∧ Real.exp ((-1063/57344 : ℝ)/8) ≤ (498842763211689591/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1063/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0075_exp_lower : (918088830441753491/1000000000000000000 : ℝ) ≤ Real.exp ((-5341320491/7812500000 : ℝ)/8) ∧ Real.exp ((-5341320491/7812500000 : ℝ)/8) ≤ (229522207610438373/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5341320491/7812500000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0075_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019006054871/1000000000000 : ℝ) ≤ 4*Real.exp (531/4096 : ℝ)*Real.exp (-mu (radius 7 (1063/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (2019006054871/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1063/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0075_exp_radius
  have hrNumeric : (490816754579/500000000000 : ℝ) ≤ Real.exp (-1063/57344 : ℝ) ∧ Real.exp (-1063/57344 : ℝ) ≤ (981633509159/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490816754579/500000000000 : ℝ) ≤ (radius 7 (1063/8192 : ℝ)) ∧ (radius 7 (1063/8192 : ℝ)) ≤ (981633509159/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1063/8192 : ℝ)) (490816754579/500000000000 : ℝ) (981633509159/1000000000000 : ℝ) (47694112383/250000000000 : ℝ) (95388224769/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1063/8192 : ℝ)) (490816754579/500000000000 : ℝ) (981633509159/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1063/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490816754579/500000000000 : ℝ) (981633509159/1000000000000 : ℝ) (990816754579/1000000000000 : ℝ) (49540837729/50000000000 : ℝ) (990774196857/1000000000000 : ℝ) (495387098429/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1063/8192 : ℝ)) 1 (990816754579/1000000000000 : ℝ) (49540837729/50000000000 : ℝ) (990774196857/1000000000000 : ℝ) (495387098429/500000000000 : ℝ) (495397737859/500000000000 : ℝ) (990795475719/1000000000000 : ℝ) (990795475489/1000000000000 : ℝ) (990795475491/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1063/8192 : ℝ)) 2 (495397737859/500000000000 : ℝ) (990795475719/1000000000000 : ℝ) (990795475489/1000000000000 : ℝ) (990795475491/1000000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1063/8192 : ℝ)) 3 (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1063/8192 : ℝ)) 4 (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1063/8192 : ℝ)) 5 (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1063/8192 : ℝ)) 6 (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1063/8192 : ℝ)) 7 (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1063/8192 : ℝ))) (47694112383/250000000000 : ℝ) (95388224769/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1063/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (47694112383/250000000000 : ℝ) (95388224769/500000000000 : ℝ) (297694112383/500000000000 : ℝ) (595388224769/1000000000000 : ℝ) (218389817489/500000000000 : ℝ) (218389817493/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1063/8192 : ℝ))) 1 (297694112383/500000000000 : ℝ) (595388224769/1000000000000 : ℝ) (218389817489/500000000000 : ℝ) (218389817493/500000000000 : ℝ) (32255245617/62500000000 : ℝ) (258041964939/500000000000 : ℝ) (509954362157/1000000000000 : ℝ) (127488590541/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1063/8192 : ℝ))) 2 (32255245617/62500000000 : ℝ) (258041964939/500000000000 : ℝ) (509954362157/1000000000000 : ℝ) (127488590541/250000000000 : ℝ) (256509573007/500000000000 : ℝ) (513019146021/1000000000000 : ℝ) (513009991401/1000000000000 : ℝ) (32063124463/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1063/8192 : ℝ))) 3 (256509573007/500000000000 : ℝ) (513019146021/1000000000000 : ℝ) (513009991401/1000000000000 : ℝ) (32063124463/62500000000 : ℝ) (513014568707/1000000000000 : ℝ) (102602913743/200000000000 : ℝ) (513014568687/1000000000000 : ℝ) (102602913739/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1063/8192 : ℝ))) 4 (513014568707/1000000000000 : ℝ) (102602913743/200000000000 : ℝ) (513014568687/1000000000000 : ℝ) (102602913739/200000000000 : ℝ) (513014568697/1000000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1063/8192 : ℝ))) 5 (513014568697/1000000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1063/8192 : ℝ))) 6 (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1063/8192 : ℝ))) 7 (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1063/8192 : ℝ)) hmem 8 (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1063/8192 : ℝ))) hcmem 8 (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1063/8192 : ℝ)) (990795475603/1000000000000 : ℝ) (198159095121/200000000000 : ℝ) (64126821087/125000000000 : ℝ) (102602913741/200000000000 : ℝ) (813327694707/1000000000000 : ℝ) (813327694723/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0075_exp_lower
  have heNumeric : (2019006054871/1000000000000 : ℝ)/4 ≤ Real.exp (-5341320491/7812500000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019006054871/1000000000000 : ℝ)/4 ≤ Real.exp ((531/4096 : ℝ)-(813327694723/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (531/4096 : ℝ) (1063/8192 : ℝ) (813327694723/1000000000000 : ℝ) (2019006054871/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0076; no trusted numerical premise.
theorem cover7_leaf0076_exp_radius : (124710554879130413/125000000000000000 : ℝ) ≤ Real.exp ((-2127/114688 : ℝ)/8) ∧ Real.exp ((-2127/114688 : ℝ)/8) ≤ (199536887806608661/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2127/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0076_exp_lower : (45904780236486153/50000000000000000 : ℝ) ≤ Real.exp ((-1367259987177/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367259987177/2000000000000 : ℝ)/8) ≤ (918095604729723061/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367259987177/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0076_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019125238821/1000000000000 : ℝ) ≤ 4*Real.exp (1063/8192 : ℝ)*Real.exp (-mu (radius 7 (2127/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019125238821/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2127/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0076_exp_radius
  have hrNumeric : (98162495003/100000000000 : ℝ) ≤ Real.exp (-2127/114688 : ℝ) ∧ Real.exp (-2127/114688 : ℝ) ≤ (981624950031/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (98162495003/100000000000 : ℝ) ≤ (radius 7 (2127/16384 : ℝ)) ∧ (radius 7 (2127/16384 : ℝ)) ≤ (981624950031/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2127/16384 : ℝ)) (98162495003/100000000000 : ℝ) (981624950031/1000000000000 : ℝ) (3816409699/20000000000 : ℝ) (47705121239/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2127/16384 : ℝ)) (98162495003/100000000000 : ℝ) (981624950031/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2127/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (98162495003/100000000000 : ℝ) (981624950031/1000000000000 : ℝ) (198162495003/200000000000 : ℝ) (123851559377/125000000000 : ℝ) (990769877433/1000000000000 : ℝ) (198153975487/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2127/16384 : ℝ)) 1 (198162495003/200000000000 : ℝ) (123851559377/125000000000 : ℝ) (990769877433/1000000000000 : ℝ) (198153975487/200000000000 : ℝ) (30962224257/31250000000 : ℝ) (495395588113/500000000000 : ℝ) (198158235199/200000000000 : ℝ) (990791175997/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2127/16384 : ℝ)) 2 (30962224257/31250000000 : ℝ) (495395588113/500000000000 : ℝ) (198158235199/200000000000 : ℝ) (990791175997/1000000000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2127/16384 : ℝ)) 3 (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2127/16384 : ℝ)) 4 (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2127/16384 : ℝ)) 5 (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2127/16384 : ℝ)) 6 (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2127/16384 : ℝ)) 7 (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2127/16384 : ℝ))) (3816409699/20000000000 : ℝ) (47705121239/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2127/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (3816409699/20000000000 : ℝ) (47705121239/250000000000 : ℝ) (23816409699/40000000000 : ℝ) (297705121239/500000000000 : ℝ) (436830041263/1000000000000 : ℝ) (436830041271/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2127/16384 : ℝ))) 1 (23816409699/40000000000 : ℝ) (297705121239/500000000000 : ℝ) (436830041263/1000000000000 : ℝ) (436830041271/1000000000000 : ℝ) (516120141869/1000000000000 : ℝ) (825792227/1600000000 : ℝ) (254996608207/500000000000 : ℝ) (509993216421/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2127/16384 : ℝ))) 2 (516120141869/1000000000000 : ℝ) (825792227/1600000000 : ℝ) (254996608207/500000000000 : ℝ) (509993216421/1000000000000 : ℝ) (513056679141/1000000000000 : ℝ) (128264169787/250000000000 : ℝ) (16032735409/31250000000 : ℝ) (102609506619/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2127/16384 : ℝ))) 3 (513056679141/1000000000000 : ℝ) (128264169787/250000000000 : ℝ) (16032735409/31250000000 : ℝ) (102609506619/200000000000 : ℝ) (256526053057/500000000000 : ℝ) (256526053061/500000000000 : ℝ) (256526053047/500000000000 : ℝ) (256526053051/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2127/16384 : ℝ))) 4 (256526053057/500000000000 : ℝ) (256526053061/500000000000 : ℝ) (256526053047/500000000000 : ℝ) (256526053051/500000000000 : ℝ) (64131513263/125000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2127/16384 : ℝ))) 5 (64131513263/125000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2127/16384 : ℝ))) 6 (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2127/16384 : ℝ))) 7 (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2127/16384 : ℝ)) hmem 8 (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2127/16384 : ℝ))) hcmem 8 (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2127/16384 : ℝ)) (990791176109/1000000000000 : ℝ) (61924448507/62500000000 : ℝ) (513052106103/1000000000000 : ℝ) (4008219579/7812500000 : ℝ) (406695367879/500000000000 : ℝ) (25418460493/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0076_exp_lower
  have heNumeric : (2019125238821/1000000000000 : ℝ)/4 ≤ Real.exp (-1367259987177/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019125238821/1000000000000 : ℝ)/4 ≤ Real.exp ((1063/8192 : ℝ)-(25418460493/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1063/8192 : ℝ) (2127/16384 : ℝ) (25418460493/31250000000 : ℝ) (2019125238821/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0077; no trusted numerical premise.
theorem cover7_leaf0077_exp_radius : (249420837910973147/250000000000000000 : ℝ) ≤ Real.exp ((-19/1024 : ℝ)/8) ∧ Real.exp ((-19/1024 : ℝ)/8) ≤ (997683351643892589/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-19/1024 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0077_exp_lower : (918095376809562357/1000000000000000000 : ℝ) ≤ Real.exp ((-2734527918457/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734527918457/4000000000000 : ℝ)/8) ≤ (459047688404781179/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734527918457/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0077_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201912122879/100000000000 : ℝ) ≤ 4*Real.exp (2127/16384 : ℝ)*Real.exp (-mu (radius 7 (133/1024 : ℝ))) ∧ (2019/1000 : ℝ) < (201912122879/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (133/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0077_exp_radius
  have hrNumeric : (981616390977/1000000000000 : ℝ) ≤ Real.exp (-19/1024 : ℝ) ∧ Real.exp (-19/1024 : ℝ) ≤ (490808195489/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981616390977/1000000000000 : ℝ) ≤ (radius 7 (133/1024 : ℝ)) ∧ (radius 7 (133/1024 : ℝ)) ≤ (490808195489/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (133/1024 : ℝ)) (981616390977/1000000000000 : ℝ) (490808195489/500000000000 : ℝ) (95432254719/500000000000 : ℝ) (47716127361/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (133/1024 : ℝ)) (981616390977/1000000000000 : ℝ) (490808195489/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (133/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981616390977/1000000000000 : ℝ) (490808195489/500000000000 : ℝ) (30962756109/31250000000 : ℝ) (990808195489/1000000000000 : ℝ) (990765558029/1000000000000 : ℝ) (99076555803/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (133/1024 : ℝ)) 1 (30962756109/31250000000 : ℝ) (990808195489/1000000000000 : ℝ) (990765558029/1000000000000 : ℝ) (99076555803/100000000000 : ℝ) (495393438379/500000000000 : ℝ) (24769671919/25000000000 : ℝ) (990786876529/1000000000000 : ℝ) (990786876531/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (133/1024 : ℝ)) 2 (495393438379/500000000000 : ℝ) (24769671919/25000000000 : ℝ) (990786876529/1000000000000 : ℝ) (990786876531/1000000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (133/1024 : ℝ)) 3 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (133/1024 : ℝ)) 4 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (133/1024 : ℝ)) 5 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (133/1024 : ℝ)) 6 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (133/1024 : ℝ)) 7 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (133/1024 : ℝ))) (95432254719/500000000000 : ℝ) (47716127361/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (133/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (95432254719/500000000000 : ℝ) (47716127361/250000000000 : ℝ) (595432254719/1000000000000 : ℝ) (297716127361/500000000000 : ℝ) (218440214611/500000000000 : ℝ) (43688042923/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (133/1024 : ℝ))) 1 (595432254719/1000000000000 : ℝ) (297716127361/500000000000 : ℝ) (218440214611/500000000000 : ℝ) (43688042923/100000000000 : ℝ) (51615634197/100000000000 : ℝ) (64519542747/125000000000 : ℝ) (510032056849/1000000000000 : ℝ) (63754007107/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (133/1024 : ℝ))) 2 (51615634197/100000000000 : ℝ) (64519542747/125000000000 : ℝ) (510032056849/1000000000000 : ℝ) (63754007107/125000000000 : ℝ) (513094199409/1000000000000 : ℝ) (64136774927/125000000000 : ℝ) (102617012381/200000000000 : ℝ) (513085061913/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (133/1024 : ℝ))) 3 (513094199409/1000000000000 : ℝ) (64136774927/125000000000 : ℝ) (102617012381/200000000000 : ℝ) (513085061913/1000000000000 : ℝ) (513089630657/1000000000000 : ℝ) (102617926133/200000000000 : ℝ) (128272407659/250000000000 : ℝ) (102617926129/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (133/1024 : ℝ))) 4 (513089630657/1000000000000 : ℝ) (102617926133/200000000000 : ℝ) (128272407659/250000000000 : ℝ) (102617926129/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (133/1024 : ℝ))) 5 (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (133/1024 : ℝ))) 6 (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (133/1024 : ℝ))) 7 (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (133/1024 : ℝ)) hmem 8 (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (133/1024 : ℝ))) hcmem 8 (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (133/1024 : ℝ)) (990786876643/1000000000000 : ℝ) (495393438323/500000000000 : ℝ) (256544815323/500000000000 : ℝ) (102617926131/200000000000 : ℝ) (40672687847/50000000000 : ℝ) (406726878479/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0077_exp_lower
  have heNumeric : (201912122879/100000000000 : ℝ)/4 ≤ Real.exp (-2734527918457/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201912122879/100000000000 : ℝ)/4 ≤ Real.exp ((2127/16384 : ℝ)-(406726878479/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2127/16384 : ℝ) (133/1024 : ℝ) (406726878479/500000000000 : ℝ) (201912122879/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0078; no trusted numerical premise.
theorem cover7_leaf0078_exp_radius : (124710283031990879/125000000000000000 : ℝ) ≤ Real.exp ((-2129/114688 : ℝ)/8) ∧ Real.exp ((-2129/114688 : ℝ)/8) ≤ (997682264255927033/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2129/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0078_exp_lower : (459047575583740913/500000000000000000 : ℝ) ≤ Real.exp ((-68363394579/100000000000 : ℝ)/8) ∧ Real.exp ((-68363394579/100000000000 : ℝ)/8) ≤ (918095151167481827/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-68363394579/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0078_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019117258847/1000000000000 : ℝ) ≤ 4*Real.exp (133/1024 : ℝ)*Real.exp (-mu (radius 7 (2129/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019117258847/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2129/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0078_exp_radius
  have hrNumeric : (981607831999/1000000000000 : ℝ) ≤ Real.exp (-2129/114688 : ℝ) ∧ Real.exp (-2129/114688 : ℝ) ≤ (122700979/125000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981607831999/1000000000000 : ℝ) ≤ (radius 7 (2129/16384 : ℝ)) ∧ (radius 7 (2129/16384 : ℝ)) ≤ (122700979/125000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2129/16384 : ℝ)) (981607831999/1000000000000 : ℝ) (122700979/125000000 : ℝ) (38181704601/200000000000 : ℝ) (190908523011/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2129/16384 : ℝ)) (981607831999/1000000000000 : ℝ) (122700979/125000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2129/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981607831999/1000000000000 : ℝ) (122700979/125000000 : ℝ) (990803915999/1000000000000 : ℝ) (247700979/250000000 : ℝ) (990761238643/1000000000000 : ℝ) (198152247729/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2129/16384 : ℝ)) 1 (990803915999/1000000000000 : ℝ) (247700979/250000000 : ℝ) (990761238643/1000000000000 : ℝ) (198152247729/200000000000 : ℝ) (990782577321/1000000000000 : ℝ) (990782577323/1000000000000 : ℝ) (990782577091/1000000000000 : ℝ) (990782577093/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2129/16384 : ℝ)) 2 (990782577321/1000000000000 : ℝ) (990782577323/1000000000000 : ℝ) (990782577091/1000000000000 : ℝ) (990782577093/1000000000000 : ℝ) (495391288603/500000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2129/16384 : ℝ)) 3 (495391288603/500000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2129/16384 : ℝ)) 4 (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2129/16384 : ℝ)) 5 (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2129/16384 : ℝ)) 6 (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2129/16384 : ℝ)) 7 (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2129/16384 : ℝ))) (38181704601/200000000000 : ℝ) (190908523011/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2129/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38181704601/200000000000 : ℝ) (190908523011/1000000000000 : ℝ) (297727130751/500000000000 : ℝ) (297727130753/500000000000 : ℝ) (218465399437/500000000000 : ℝ) (218465399441/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2129/16384 : ℝ))) 1 (297727130751/500000000000 : ℝ) (297727130753/500000000000 : ℝ) (218465399437/500000000000 : ℝ) (218465399441/500000000000 : ℝ) (129048132547/250000000000 : ℝ) (258096265097/500000000000 : ℝ) (127517720869/250000000000 : ℝ) (127517720871/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2129/16384 : ℝ))) 2 (129048132547/250000000000 : ℝ) (258096265097/500000000000 : ℝ) (127517720869/250000000000 : ℝ) (127517720871/250000000000 : ℝ) (32070731677/62500000000 : ℝ) (513131706839/1000000000000 : ℝ) (256561288933/500000000000 : ℝ) (256561288937/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2129/16384 : ℝ))) 3 (32070731677/62500000000 : ℝ) (513131706839/1000000000000 : ℝ) (256561288933/500000000000 : ℝ) (256561288937/500000000000 : ℝ) (513127142349/1000000000000 : ℝ) (513127142357/1000000000000 : ℝ) (64140892791/125000000000 : ℝ) (513127142337/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2129/16384 : ℝ))) 4 (513127142349/1000000000000 : ℝ) (513127142357/1000000000000 : ℝ) (64140892791/125000000000 : ℝ) (513127142337/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2129/16384 : ℝ))) 5 (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2129/16384 : ℝ))) 6 (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2129/16384 : ℝ))) 7 (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2129/16384 : ℝ)) hmem 8 (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2129/16384 : ℝ))) hcmem 8 (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2129/16384 : ℝ)) (198156515441/200000000000 : ℝ) (123847822151/125000000000 : ℝ) (256563571169/500000000000 : ℝ) (513127142347/1000000000000 : ℝ) (3177799837/3906250000 : ℝ) (81351675829/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0078_exp_lower
  have heNumeric : (2019117258847/1000000000000 : ℝ)/4 ≤ Real.exp (-68363394579/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019117258847/1000000000000 : ℝ)/4 ≤ Real.exp ((133/1024 : ℝ)-(81351675829/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (133/1024 : ℝ) (2129/16384 : ℝ) (81351675829/100000000000 : ℝ) (2019117258847/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0079; no trusted numerical premise.
theorem cover7_leaf0079_exp_radius : (498840588434573317/500000000000000000 : ℝ) ≤ Real.exp ((-1065/57344 : ℝ)/8) ∧ Real.exp ((-1065/57344 : ℝ)/8) ≤ (199536235373829327/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1065/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0079_exp_lower : (114761865975148069/125000000000000000 : ℝ) ≤ Real.exp ((-2734543568543/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734543568543/4000000000000 : ℝ)/8) ≤ (918094927801184553/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734543568543/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0079_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (40382266579/20000000000 : ℝ) ≤ 4*Real.exp (2129/16384 : ℝ)*Real.exp (-mu (radius 7 (1065/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (40382266579/20000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1065/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0079_exp_radius
  have hrNumeric : (196319854619/200000000000 : ℝ) ≤ Real.exp (-1065/57344 : ℝ) ∧ Real.exp (-1065/57344 : ℝ) ≤ (122699909137/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196319854619/200000000000 : ℝ) ≤ (radius 7 (1065/8192 : ℝ)) ∧ (radius 7 (1065/8192 : ℝ)) ≤ (122699909137/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1065/8192 : ℝ)) (196319854619/200000000000 : ℝ) (122699909137/125000000000 : ℝ) (190952525663/1000000000000 : ℝ) (190952525669/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1065/8192 : ℝ)) (196319854619/200000000000 : ℝ) (122699909137/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1065/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196319854619/200000000000 : ℝ) (122699909137/125000000000 : ℝ) (990799636547/1000000000000 : ℝ) (247699909137/250000000000 : ℝ) (247689229819/250000000000 : ℝ) (495378459639/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1065/8192 : ℝ)) 1 (990799636547/1000000000000 : ℝ) (247699909137/250000000000 : ℝ) (247689229819/250000000000 : ℝ) (495378459639/500000000000 : ℝ) (990778277911/1000000000000 : ℝ) (990778277913/1000000000000 : ℝ) (990778277681/1000000000000 : ℝ) (990778277683/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1065/8192 : ℝ)) 2 (990778277911/1000000000000 : ℝ) (990778277913/1000000000000 : ℝ) (990778277681/1000000000000 : ℝ) (990778277683/1000000000000 : ℝ) (247694569449/250000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1065/8192 : ℝ)) 3 (247694569449/250000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1065/8192 : ℝ)) 4 (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1065/8192 : ℝ)) 5 (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1065/8192 : ℝ)) 6 (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1065/8192 : ℝ)) 7 (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1065/8192 : ℝ))) (190952525663/1000000000000 : ℝ) (190952525669/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1065/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (190952525663/1000000000000 : ℝ) (190952525669/1000000000000 : ℝ) (595476262831/1000000000000 : ℝ) (119095252567/200000000000 : ℝ) (436981150237/1000000000000 : ℝ) (87396230049/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1065/8192 : ℝ))) 1 (595476262831/1000000000000 : ℝ) (119095252567/200000000000 : ℝ) (436981150237/1000000000000 : ℝ) (87396230049/200000000000 : ℝ) (258114353267/500000000000 : ℝ) (25811435327/50000000000 : ℝ) (510109696311/1000000000000 : ℝ) (255054848159/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1065/8192 : ℝ))) 2 (258114353267/500000000000 : ℝ) (25811435327/50000000000 : ℝ) (510109696311/1000000000000 : ℝ) (255054848159/500000000000 : ℝ) (256584600711/500000000000 : ℝ) (513169201429/1000000000000 : ℝ) (102632016197/200000000000 : ℝ) (513160080993/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1065/8192 : ℝ))) 3 (256584600711/500000000000 : ℝ) (513169201429/1000000000000 : ℝ) (102632016197/200000000000 : ℝ) (513160080993/1000000000000 : ℝ) (513164641203/1000000000000 : ℝ) (513164641211/1000000000000 : ℝ) (513164641183/1000000000000 : ℝ) (513164641191/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1065/8192 : ℝ))) 4 (513164641203/1000000000000 : ℝ) (513164641211/1000000000000 : ℝ) (513164641183/1000000000000 : ℝ) (513164641191/1000000000000 : ℝ) (513164641193/1000000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1065/8192 : ℝ))) 5 (513164641193/1000000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1065/8192 : ℝ))) 6 (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1065/8192 : ℝ))) 7 (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1065/8192 : ℝ)) hmem 8 (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1065/8192 : ℝ))) hcmem 8 (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1065/8192 : ℝ)) (198155655559/200000000000 : ℝ) (495389138899/500000000000 : ℝ) (64145580149/125000000000 : ℝ) (513164641201/1000000000000 : ℝ) (406789869887/500000000000 : ℝ) (50848733737/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0079_exp_lower
  have heNumeric : (40382266579/20000000000 : ℝ)/4 ≤ Real.exp (-2734543568543/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (40382266579/20000000000 : ℝ)/4 ≤ Real.exp ((2129/16384 : ℝ)-(50848733737/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2129/16384 : ℝ) (1065/8192 : ℝ) (50848733737/62500000000 : ℝ) (40382266579/20000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0080; no trusted numerical premise.
theorem cover7_leaf0080_exp_radius : (31177502796360981/31250000000000000 : ℝ) ≤ Real.exp ((-2131/114688 : ℝ)/8) ∧ Real.exp ((-2131/114688 : ℝ)/8) ≤ (997680089483551393/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0080_exp_lower : (91809470670929173/100000000000000000 : ℝ) ≤ Real.exp ((-1367275637327/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367275637327/2000000000000 : ℝ)/8) ≤ (918094706709291731/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367275637327/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0080_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504777359769/250000000000 : ℝ) ≤ 4*Real.exp (1065/8192 : ℝ)*Real.exp (-mu (radius 7 (2131/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (504777359769/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2131/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0080_exp_radius
  have hrNumeric : (490795357133/500000000000 : ℝ) ≤ Real.exp (-2131/114688 : ℝ) ∧ Real.exp (-2131/114688 : ℝ) ≤ (981590714267/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490795357133/500000000000 : ℝ) ≤ (radius 7 (2131/16384 : ℝ)) ∧ (radius 7 (2131/16384 : ℝ)) ≤ (981590714267/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2131/16384 : ℝ)) (490795357133/500000000000 : ℝ) (981590714267/1000000000000 : ℝ) (38199303483/200000000000 : ℝ) (190996517421/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2131/16384 : ℝ)) (490795357133/500000000000 : ℝ) (981590714267/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2131/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490795357133/500000000000 : ℝ) (981590714267/1000000000000 : ℝ) (990795357133/1000000000000 : ℝ) (495397678567/500000000000 : ℝ) (123844074991/125000000000 : ℝ) (99075259993/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2131/16384 : ℝ)) 1 (990795357133/1000000000000 : ℝ) (495397678567/500000000000 : ℝ) (123844074991/125000000000 : ℝ) (99075259993/100000000000 : ℝ) (99077397853/100000000000 : ℝ) (247693494633/250000000000 : ℝ) (990773978299/1000000000000 : ℝ) (495386989151/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2131/16384 : ℝ)) 2 (99077397853/100000000000 : ℝ) (247693494633/250000000000 : ℝ) (990773978299/1000000000000 : ℝ) (495386989151/500000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2131/16384 : ℝ)) 3 (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2131/16384 : ℝ)) 4 (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2131/16384 : ℝ)) 5 (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2131/16384 : ℝ)) 6 (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2131/16384 : ℝ)) 7 (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2131/16384 : ℝ))) (38199303483/200000000000 : ℝ) (190996517421/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2131/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38199303483/200000000000 : ℝ) (190996517421/1000000000000 : ℝ) (595498258707/1000000000000 : ℝ) (595498258711/1000000000000 : ℝ) (218515741661/500000000000 : ℝ) (43703148333/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2131/16384 : ℝ))) 1 (595498258707/1000000000000 : ℝ) (595498258711/1000000000000 : ℝ) (218515741661/500000000000 : ℝ) (43703148333/100000000000 : ℝ) (258132435507/500000000000 : ℝ) (516264871021/1000000000000 : ℝ) (49819189/97656250 : ℝ) (510148495367/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2131/16384 : ℝ))) 2 (258132435507/500000000000 : ℝ) (516264871021/1000000000000 : ℝ) (49819189/97656250 : ℝ) (510148495367/1000000000000 : ℝ) (513206683187/1000000000000 : ℝ) (256603341597/500000000000 : ℝ) (513197571267/1000000000000 : ℝ) (20527902851/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2131/16384 : ℝ))) 3 (513206683187/1000000000000 : ℝ) (256603341597/500000000000 : ℝ) (513197571267/1000000000000 : ℝ) (20527902851/40000000000 : ℝ) (513202127227/1000000000000 : ℝ) (102640425447/200000000000 : ℝ) (256601063603/500000000000 : ℝ) (102640425443/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2131/16384 : ℝ))) 4 (513202127227/1000000000000 : ℝ) (102640425447/200000000000 : ℝ) (256601063603/500000000000 : ℝ) (102640425443/200000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2131/16384 : ℝ))) 5 (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2131/16384 : ℝ))) 6 (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2131/16384 : ℝ))) 7 (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2131/16384 : ℝ)) hmem 8 (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2131/16384 : ℝ))) hcmem 8 (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2131/16384 : ℝ)) (495386989207/500000000000 : ℝ) (990773978417/1000000000000 : ℝ) (32075132951/62500000000 : ℝ) (20528085089/40000000000 : ℝ) (406821350729/500000000000 : ℝ) (203410675369/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0080_exp_lower
  have heNumeric : (504777359769/250000000000 : ℝ)/4 ≤ Real.exp (-1367275637327/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504777359769/250000000000 : ℝ)/4 ≤ Real.exp ((1065/8192 : ℝ)-(203410675369/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1065/8192 : ℝ) (2131/16384 : ℝ) (203410675369/250000000000 : ℝ) (504777359769/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0081; no trusted numerical premise.
theorem cover7_leaf0081_exp_radius : (997679002099141307/1000000000000000000 : ℝ) ≤ Real.exp ((-533/28672 : ℝ)/8) ∧ Real.exp ((-533/28672 : ℝ)/8) ≤ (249419750524785327/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-533/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0081_exp_lower : (459047243944753241/500000000000000000 : ℝ) ≤ Real.exp ((-2734558901573/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734558901573/4000000000000 : ℝ)/8) ≤ (918094487889506483/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734558901573/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0081_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (31548524831/15625000000 : ℝ) ≤ 4*Real.exp (2131/16384 : ℝ)*Real.exp (-mu (radius 7 (533/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (31548524831/15625000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (533/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0081_exp_radius
  have hrNumeric : (981582155511/1000000000000 : ℝ) ≤ Real.exp (-533/28672 : ℝ) ∧ Real.exp (-533/28672 : ℝ) ≤ (122697769439/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981582155511/1000000000000 : ℝ) ≤ (radius 7 (533/4096 : ℝ)) ∧ (radius 7 (533/4096 : ℝ)) ≤ (122697769439/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (533/4096 : ℝ)) (981582155511/1000000000000 : ℝ) (122697769439/125000000000 : ℝ) (191040498273/1000000000000 : ℝ) (191040498279/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (533/4096 : ℝ)) (981582155511/1000000000000 : ℝ) (122697769439/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (533/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981582155511/1000000000000 : ℝ) (122697769439/125000000000 : ℝ) (198158215551/200000000000 : ℝ) (247697769439/250000000000 : ℝ) (990748280599/1000000000000 : ℝ) (990748280601/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (533/4096 : ℝ)) 1 (198158215551/200000000000 : ℝ) (247697769439/250000000000 : ℝ) (990748280599/1000000000000 : ℝ) (990748280601/1000000000000 : ℝ) (990769679177/1000000000000 : ℝ) (990769679179/1000000000000 : ℝ) (198153935789/200000000000 : ℝ) (247692419737/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (533/4096 : ℝ)) 2 (990769679177/1000000000000 : ℝ) (990769679179/1000000000000 : ℝ) (198153935789/200000000000 : ℝ) (247692419737/250000000000 : ℝ) (990769679061/1000000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (533/4096 : ℝ)) 3 (990769679061/1000000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (533/4096 : ℝ)) 4 (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (533/4096 : ℝ)) 5 (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (533/4096 : ℝ)) 6 (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (533/4096 : ℝ)) 7 (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (533/4096 : ℝ))) (191040498273/1000000000000 : ℝ) (191040498279/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (533/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191040498273/1000000000000 : ℝ) (191040498279/1000000000000 : ℝ) (37220015571/62500000000 : ℝ) (29776012457/50000000000 : ℝ) (109270449537/250000000000 : ℝ) (109270449539/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (533/4096 : ℝ))) 1 (37220015571/62500000000 : ℝ) (29776012457/50000000000 : ℝ) (109270449537/250000000000 : ℝ) (109270449539/250000000000 : ℝ) (258150511821/500000000000 : ℝ) (16134406989/31250000000 : ℝ) (510187280639/1000000000000 : ℝ) (255093640323/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (533/4096 : ℝ))) 2 (258150511821/500000000000 : ℝ) (16134406989/31250000000 : ℝ) (510187280639/1000000000000 : ℝ) (255093640323/500000000000 : ℝ) (25662207607/50000000000 : ℝ) (513244152147/1000000000000 : ℝ) (64154381091/125000000000 : ℝ) (102647009747/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (533/4096 : ℝ))) 3 (25662207607/50000000000 : ℝ) (513244152147/1000000000000 : ℝ) (64154381091/125000000000 : ℝ) (102647009747/200000000000 : ℝ) (256619800217/500000000000 : ℝ) (513239600441/1000000000000 : ℝ) (513239600413/1000000000000 : ℝ) (513239600421/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (533/4096 : ℝ))) 4 (256619800217/500000000000 : ℝ) (513239600441/1000000000000 : ℝ) (513239600413/1000000000000 : ℝ) (513239600421/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (533/4096 : ℝ))) 5 (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (533/4096 : ℝ))) 6 (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (533/4096 : ℝ))) 7 (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (533/4096 : ℝ)) hmem 8 (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (533/4096 : ℝ))) hcmem 8 (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (533/4096 : ℝ)) (49538483953/50000000000 : ℝ) (123846209883/125000000000 : ℝ) (513239600423/1000000000000 : ℝ) (513239600431/1000000000000 : ℝ) (162741128669/200000000000 : ℝ) (406852821681/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0081_exp_lower
  have heNumeric : (31548524831/15625000000 : ℝ)/4 ≤ Real.exp (-2734558901573/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (31548524831/15625000000 : ℝ)/4 ≤ Real.exp ((2131/16384 : ℝ)-(406852821681/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2131/16384 : ℝ) (533/4096 : ℝ) (406852821681/500000000000 : ℝ) (31548524831/15625000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0082; no trusted numerical premise.
theorem cover7_leaf0082_exp_radius : (7981423317727331/8000000000000000 : ℝ) ≤ Real.exp ((-2133/114688 : ℝ)/8) ∧ Real.exp ((-2133/114688 : ℝ)/8) ≤ (124709739339489547/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2133/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0082_exp_lower : (918094271340335279/1000000000000000000 : ℝ) ≤ Real.exp ((-341820806169/500000000000 : ℝ)/8) ∧ Real.exp ((-341820806169/500000000000 : ℝ)/8) ≤ (11476178391754191/12500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341820806169/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0082_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019101779247/1000000000000 : ℝ) ≤ 4*Real.exp (533/4096 : ℝ)*Real.exp (-mu (radius 7 (2133/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019101779247/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2133/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0082_exp_radius
  have hrNumeric : (981573596831/1000000000000 : ℝ) ≤ Real.exp (-2133/114688 : ℝ) ∧ Real.exp (-2133/114688 : ℝ) ≤ (30674174901/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981573596831/1000000000000 : ℝ) ≤ (radius 7 (2133/16384 : ℝ)) ∧ (radius 7 (2133/16384 : ℝ)) ≤ (30674174901/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2133/16384 : ℝ)) (981573596831/1000000000000 : ℝ) (30674174901/31250000000 : ℝ) (191084468239/1000000000000 : ℝ) (38216893649/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2133/16384 : ℝ)) (981573596831/1000000000000 : ℝ) (30674174901/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2133/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981573596831/1000000000000 : ℝ) (30674174901/31250000000 : ℝ) (198157359683/200000000000 : ℝ) (61924174901/62500000000 : ℝ) (990743961289/1000000000000 : ℝ) (99074396129/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2133/16384 : ℝ)) 1 (198157359683/200000000000 : ℝ) (61924174901/62500000000 : ℝ) (990743961289/1000000000000 : ℝ) (99074396129/100000000000 : ℝ) (247691344963/250000000000 : ℝ) (990765379853/1000000000000 : ℝ) (49538268981/50000000000 : ℝ) (495382689811/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2133/16384 : ℝ)) 2 (247691344963/250000000000 : ℝ) (990765379853/1000000000000 : ℝ) (49538268981/50000000000 : ℝ) (495382689811/500000000000 : ℝ) (123845672467/125000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2133/16384 : ℝ)) 3 (123845672467/125000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2133/16384 : ℝ)) 4 (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2133/16384 : ℝ)) 5 (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2133/16384 : ℝ)) 6 (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2133/16384 : ℝ)) 7 (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2133/16384 : ℝ))) (191084468239/1000000000000 : ℝ) (38216893649/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2133/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191084468239/1000000000000 : ℝ) (38216893649/200000000000 : ℝ) (595542234119/1000000000000 : ℝ) (595542234123/1000000000000 : ℝ) (17485283789/40000000000 : ℝ) (437132094733/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2133/16384 : ℝ))) 1 (595542234119/1000000000000 : ℝ) (595542234123/1000000000000 : ℝ) (17485283789/40000000000 : ℝ) (437132094733/1000000000000 : ℝ) (258168582211/500000000000 : ℝ) (129084291107/250000000000 : ℝ) (255113026077/500000000000 : ℝ) (255113026081/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2133/16384 : ℝ))) 2 (258168582211/500000000000 : ℝ) (129084291107/250000000000 : ℝ) (255113026077/500000000000 : ℝ) (255113026081/500000000000 : ℝ) (16040050259/31250000000 : ℝ) (102656321659/200000000000 : ℝ) (128318128343/250000000000 : ℝ) (25663625669/50000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2133/16384 : ℝ))) 3 (16040050259/31250000000 : ℝ) (102656321659/200000000000 : ℝ) (128318128343/250000000000 : ℝ) (25663625669/50000000000 : ℝ) (51327706083/100000000000 : ℝ) (256638530419/500000000000 : ℝ) (513277060809/1000000000000 : ℝ) (256638530409/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2133/16384 : ℝ))) 4 (51327706083/100000000000 : ℝ) (256638530419/500000000000 : ℝ) (513277060809/1000000000000 : ℝ) (256638530409/500000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2133/16384 : ℝ))) 5 (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2133/16384 : ℝ))) 6 (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2133/16384 : ℝ))) 7 (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2133/16384 : ℝ)) hmem 8 (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2133/16384 : ℝ))) hcmem 8 (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2133/16384 : ℝ)) (198153075947/200000000000 : ℝ) (495382689869/500000000000 : ℝ) (513277060819/1000000000000 : ℝ) (128319265207/250000000000 : ℝ) (162753713089/200000000000 : ℝ) (813768565463/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0082_exp_lower
  have heNumeric : (2019101779247/1000000000000 : ℝ)/4 ≤ Real.exp (-341820806169/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019101779247/1000000000000 : ℝ)/4 ≤ Real.exp ((533/4096 : ℝ)-(813768565463/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (533/4096 : ℝ) (2133/16384 : ℝ) (813768565463/1000000000000 : ℝ) (2019101779247/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0083; no trusted numerical premise.
theorem cover7_leaf0083_exp_radius : (997676827333876597/1000000000000000000 : ℝ) ≤ Real.exp ((-1067/57344 : ℝ)/8) ∧ Real.exp ((-1067/57344 : ℝ)/8) ≤ (498838413666938299/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1067/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0083_exp_lower : (1468950491296639/1600000000000000 : ℝ) ≤ Real.exp ((-2734573918039/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734573918039/4000000000000 : ℝ)/8) ≤ (57380878566274961/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734573918039/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0083_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (50477450231/25000000000 : ℝ) ≤ 4*Real.exp (2133/16384 : ℝ)*Real.exp (-mu (radius 7 (1067/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (50477450231/25000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1067/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0083_exp_radius
  have hrNumeric : (490782519113/500000000000 : ℝ) ≤ Real.exp (-1067/57344 : ℝ) ∧ Real.exp (-1067/57344 : ℝ) ≤ (981565038227/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490782519113/500000000000 : ℝ) ≤ (radius 7 (1067/8192 : ℝ)) ∧ (radius 7 (1067/8192 : ℝ)) ≤ (981565038227/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1067/8192 : ℝ)) (490782519113/500000000000 : ℝ) (981565038227/1000000000000 : ℝ) (191128427321/1000000000000 : ℝ) (191128427327/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1067/8192 : ℝ)) (490782519113/500000000000 : ℝ) (981565038227/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1067/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490782519113/500000000000 : ℝ) (981565038227/1000000000000 : ℝ) (990782519113/1000000000000 : ℝ) (495391259557/500000000000 : ℝ) (990739641997/1000000000000 : ℝ) (990739641999/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1067/8192 : ℝ)) 1 (990782519113/1000000000000 : ℝ) (495391259557/500000000000 : ℝ) (990739641997/1000000000000 : ℝ) (990739641999/1000000000000 : ℝ) (198152216111/200000000000 : ℝ) (990761080557/1000000000000 : ℝ) (990761080323/1000000000000 : ℝ) (39630443213/40000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1067/8192 : ℝ)) 2 (198152216111/200000000000 : ℝ) (990761080557/1000000000000 : ℝ) (990761080323/1000000000000 : ℝ) (39630443213/40000000000 : ℝ) (990761080439/1000000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1067/8192 : ℝ)) 3 (990761080439/1000000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1067/8192 : ℝ)) 4 (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1067/8192 : ℝ)) 5 (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1067/8192 : ℝ)) 6 (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1067/8192 : ℝ)) 7 (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1067/8192 : ℝ))) (191128427321/1000000000000 : ℝ) (191128427327/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1067/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191128427321/1000000000000 : ℝ) (191128427327/1000000000000 : ℝ) (29778210683/50000000000 : ℝ) (18611381677/31250000000 : ℝ) (437182373067/1000000000000 : ℝ) (17487294923/40000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1067/8192 : ℝ))) 1 (29778210683/50000000000 : ℝ) (18611381677/31250000000 : ℝ) (437182373067/1000000000000 : ℝ) (17487294923/40000000000 : ℝ) (516373293363/1000000000000 : ℝ) (51637329337/100000000000 : ℝ) (255132404959/500000000000 : ℝ) (255132404963/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1067/8192 : ℝ))) 2 (516373293363/1000000000000 : ℝ) (51637329337/100000000000 : ℝ) (255132404959/500000000000 : ℝ) (255132404963/500000000000 : ℝ) (12832976291/25000000000 : ℝ) (4010305091/7812500000 : ℝ) (51330996521/100000000000 : ℝ) (513309965219/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1067/8192 : ℝ))) 3 (12832976291/25000000000 : ℝ) (4010305091/7812500000 : ℝ) (51330996521/100000000000 : ℝ) (513309965219/1000000000000 : ℝ) (20532580337/40000000000 : ℝ) (256657254217/500000000000 : ℝ) (128328627101/250000000000 : ℝ) (256657254207/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1067/8192 : ℝ))) 4 (20532580337/40000000000 : ℝ) (256657254217/500000000000 : ℝ) (128328627101/250000000000 : ℝ) (256657254207/500000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1067/8192 : ℝ))) 5 (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1067/8192 : ℝ))) 6 (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1067/8192 : ℝ))) 7 (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1067/8192 : ℝ)) hmem 8 (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1067/8192 : ℝ))) hcmem 8 (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1067/8192 : ℝ)) (495380540219/500000000000 : ℝ) (990761080441/1000000000000 : ℝ) (256657254207/500000000000 : ℝ) (64164313553/125000000000 : ℝ) (203457866943/250000000000 : ℝ) (813831467791/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0083_exp_lower
  have heNumeric : (50477450231/25000000000 : ℝ)/4 ≤ Real.exp (-2734573918039/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (50477450231/25000000000 : ℝ)/4 ≤ Real.exp ((2133/16384 : ℝ)-(813831467791/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2133/16384 : ℝ) (1067/8192 : ℝ) (813831467791/1000000000000 : ℝ) (50477450231/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0084; no trusted numerical premise.
theorem cover7_leaf0084_exp_radius : (99767573995302197/100000000000000000 : ℝ) ≤ Real.exp ((-305/16384 : ℝ)/8) ∧ Real.exp ((-305/16384 : ℝ)/8) ≤ (997675739953021971/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-305/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0084_exp_lower : (918093845047516707/1000000000000000000 : ℝ) ≤ Real.exp ((-273458130771/400000000000 : ℝ)/8) ∧ Real.exp ((-273458130771/400000000000 : ℝ)/8) ≤ (229523461261879177/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273458130771/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0084_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009547139563/500000000000 : ℝ) ≤ 4*Real.exp (1067/8192 : ℝ)*Real.exp (-mu (radius 7 (2135/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009547139563/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2135/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0084_exp_radius
  have hrNumeric : (61347279981/62500000000 : ℝ) ≤ Real.exp (-305/16384 : ℝ) ∧ Real.exp (-305/16384 : ℝ) ≤ (981556479697/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61347279981/62500000000 : ℝ) ≤ (radius 7 (2135/16384 : ℝ)) ∧ (radius 7 (2135/16384 : ℝ)) ≤ (981556479697/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2135/16384 : ℝ)) (61347279981/62500000000 : ℝ) (981556479697/1000000000000 : ℝ) (191172375527/1000000000000 : ℝ) (191172375533/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2135/16384 : ℝ)) (61347279981/62500000000 : ℝ) (981556479697/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2135/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61347279981/62500000000 : ℝ) (981556479697/1000000000000 : ℝ) (123847279981/125000000000 : ℝ) (990778239849/1000000000000 : ℝ) (39629412909/40000000000 : ℝ) (990735322727/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2135/16384 : ℝ)) 1 (123847279981/125000000000 : ℝ) (990778239849/1000000000000 : ℝ) (39629412909/40000000000 : ℝ) (990735322727/1000000000000 : ℝ) (495378390643/500000000000 : ℝ) (123844597661/125000000000 : ℝ) (495378390527/500000000000 : ℝ) (967535919/976562500 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2135/16384 : ℝ)) 2 (495378390643/500000000000 : ℝ) (123844597661/125000000000 : ℝ) (495378390527/500000000000 : ℝ) (967535919/976562500 : ℝ) (99075678117/100000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2135/16384 : ℝ)) 3 (99075678117/100000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2135/16384 : ℝ)) 4 (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2135/16384 : ℝ)) 5 (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2135/16384 : ℝ)) 6 (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2135/16384 : ℝ)) 7 (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2135/16384 : ℝ))) (191172375527/1000000000000 : ℝ) (191172375533/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2135/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191172375527/1000000000000 : ℝ) (191172375533/1000000000000 : ℝ) (595586187763/1000000000000 : ℝ) (595586187767/1000000000000 : ℝ) (43723263319/100000000000 : ℝ) (218616316599/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2135/16384 : ℝ))) 1 (595586187763/1000000000000 : ℝ) (595586187767/1000000000000 : ℝ) (43723263319/100000000000 : ℝ) (218616316599/500000000000 : ℝ) (129102352619/250000000000 : ℝ) (516409410483/1000000000000 : ℝ) (510303553943/1000000000000 : ℝ) (10206071079/20000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2135/16384 : ℝ))) 2 (129102352619/250000000000 : ℝ) (516409410483/1000000000000 : ℝ) (510303553943/1000000000000 : ℝ) (10206071079/20000000000 : ℝ) (513356482209/1000000000000 : ℝ) (513356482217/1000000000000 : ℝ) (102669480851/200000000000 : ℝ) (513347404263/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2135/16384 : ℝ))) 3 (513356482209/1000000000000 : ℝ) (513356482217/1000000000000 : ℝ) (102669480851/200000000000 : ℝ) (513347404263/1000000000000 : ℝ) (8021124113/15625000000 : ℝ) (12833798581/25000000000 : ℝ) (513351943211/1000000000000 : ℝ) (25667597161/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2135/16384 : ℝ))) 4 (8021124113/15625000000 : ℝ) (12833798581/25000000000 : ℝ) (513351943211/1000000000000 : ℝ) (25667597161/50000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2135/16384 : ℝ))) 5 (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2135/16384 : ℝ))) 6 (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2135/16384 : ℝ))) 7 (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2135/16384 : ℝ)) hmem 8 (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2135/16384 : ℝ))) hcmem 8 (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2135/16384 : ℝ)) (990756781169/1000000000000 : ℝ) (247689195293/250000000000 : ℝ) (513351943221/1000000000000 : ℝ) (51335194323/100000000000 : ℝ) (813894350347/1000000000000 : ℝ) (162778870073/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0084_exp_lower
  have heNumeric : (1009547139563/500000000000 : ℝ)/4 ≤ Real.exp (-273458130771/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009547139563/500000000000 : ℝ)/4 ≤ Real.exp ((1067/8192 : ℝ)-(162778870073/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1067/8192 : ℝ) (2135/16384 : ℝ) (162778870073/200000000000 : ℝ) (1009547139563/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0085; no trusted numerical premise.
theorem cover7_leaf0085_exp_radius : (498837326286676247/500000000000000000 : ℝ) ≤ Real.exp ((-267/14336 : ℝ)/8) ∧ Real.exp ((-267/14336 : ℝ)/8) ≤ (199534930514670499/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-267/14336 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0085_exp_lower : (28690426103091607/31250000000000000 : ℝ) ≤ Real.exp ((-2734588618461/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734588618461/4000000000000 : ℝ)/8) ≤ (36723745411957257/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734588618461/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0085_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252386323607/125000000000 : ℝ) ≤ 4*Real.exp (2135/16384 : ℝ)*Real.exp (-mu (radius 7 (267/2048 : ℝ))) ∧ (2019/1000 : ℝ) < (252386323607/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (267/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0085_exp_radius
  have hrNumeric : (24538698031/25000000000 : ℝ) ≤ Real.exp (-267/14336 : ℝ) ∧ Real.exp (-267/14336 : ℝ) ≤ (981547921241/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24538698031/25000000000 : ℝ) ≤ (radius 7 (267/2048 : ℝ)) ∧ (radius 7 (267/2048 : ℝ)) ≤ (981547921241/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (267/2048 : ℝ)) (24538698031/25000000000 : ℝ) (981547921241/1000000000000 : ℝ) (191216312869/1000000000000 : ℝ) (1529730503/8000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (267/2048 : ℝ)) (24538698031/25000000000 : ℝ) (981547921241/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (267/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24538698031/25000000000 : ℝ) (981547921241/1000000000000 : ℝ) (49538698031/50000000000 : ℝ) (990773960621/1000000000000 : ℝ) (990731003471/1000000000000 : ℝ) (990731003473/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (267/2048 : ℝ)) 1 (49538698031/50000000000 : ℝ) (990773960621/1000000000000 : ℝ) (990731003471/1000000000000 : ℝ) (990731003473/1000000000000 : ℝ) (198150496409/200000000000 : ℝ) (990752482047/1000000000000 : ℝ) (247688120453/250000000000 : ℝ) (198150496363/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (267/2048 : ℝ)) 2 (198150496409/200000000000 : ℝ) (990752482047/1000000000000 : ℝ) (247688120453/250000000000 : ℝ) (198150496363/200000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (267/2048 : ℝ)) 3 (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (267/2048 : ℝ)) 4 (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (267/2048 : ℝ)) 5 (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (267/2048 : ℝ)) 6 (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (267/2048 : ℝ)) 7 (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (267/2048 : ℝ))) (191216312869/1000000000000 : ℝ) (1529730503/8000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (267/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191216312869/1000000000000 : ℝ) (1529730503/8000000000 : ℝ) (297804078217/500000000000 : ℝ) (297804078219/500000000000 : ℝ) (87456575023/200000000000 : ℝ) (437282875123/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (267/2048 : ℝ))) 1 (297804078217/500000000000 : ℝ) (297804078219/500000000000 : ℝ) (87456575023/200000000000 : ℝ) (437282875123/1000000000000 : ℝ) (258222757887/500000000000 : ℝ) (516445515781/1000000000000 : ℝ) (127585571061/250000000000 : ℝ) (510342284251/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (267/2048 : ℝ))) 2 (258222757887/500000000000 : ℝ) (516445515781/1000000000000 : ℝ) (127585571061/250000000000 : ℝ) (510342284251/1000000000000 : ℝ) (513393900009/1000000000000 : ℝ) (32087118751/62500000000 : ℝ) (513384830519/1000000000000 : ℝ) (513384830527/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (267/2048 : ℝ))) 3 (513393900009/1000000000000 : ℝ) (32087118751/62500000000 : ℝ) (513384830519/1000000000000 : ℝ) (513384830527/1000000000000 : ℝ) (32086835329/62500000000 : ℝ) (64173670659/125000000000 : ℝ) (513389365243/1000000000000 : ℝ) (128347341313/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (267/2048 : ℝ))) 4 (32086835329/62500000000 : ℝ) (64173670659/125000000000 : ℝ) (513389365243/1000000000000 : ℝ) (128347341313/250000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (267/2048 : ℝ))) 5 (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (267/2048 : ℝ))) 6 (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (267/2048 : ℝ))) 7 (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (267/2048 : ℝ)) hmem 8 (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (267/2048 : ℝ))) hcmem 8 (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (267/2048 : ℝ)) (123844060241/125000000000 : ℝ) (990752481931/1000000000000 : ℝ) (513389365253/1000000000000 : ℝ) (256694682631/500000000000 : ℝ) (813957213191/1000000000000 : ℝ) (813957213209/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0085_exp_lower
  have heNumeric : (252386323607/125000000000 : ℝ)/4 ≤ Real.exp (-2734588618461/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252386323607/125000000000 : ℝ)/4 ≤ Real.exp ((2135/16384 : ℝ)-(813957213209/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2135/16384 : ℝ) (267/2048 : ℝ) (813957213209/1000000000000 : ℝ) (252386323607/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0086; no trusted numerical premise.
theorem cover7_leaf0086_exp_radius : (997673565194868167/1000000000000000000 : ℝ) ≤ Real.exp ((-2137/114688 : ℝ)/8) ∧ Real.exp ((-2137/114688 : ℝ)/8) ≤ (124709195649358521/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2137/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0086_exp_lower : (114761678476643759/125000000000000000 : ℝ) ≤ Real.exp ((-341824481293/500000000000 : ℝ)/8) ∧ Real.exp ((-341824481293/500000000000 : ℝ)/8) ≤ (918093427813150073/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-341824481293/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0086_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009543469201/500000000000 : ℝ) ≤ 4*Real.exp (267/2048 : ℝ)*Real.exp (-mu (radius 7 (2137/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009543469201/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2137/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0086_exp_radius
  have hrNumeric : (490769681429/500000000000 : ℝ) ≤ Real.exp (-2137/114688 : ℝ) ∧ Real.exp (-2137/114688 : ℝ) ≤ (981539362859/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490769681429/500000000000 : ℝ) ≤ (radius 7 (2137/16384 : ℝ)) ∧ (radius 7 (2137/16384 : ℝ)) ≤ (981539362859/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2137/16384 : ℝ)) (490769681429/500000000000 : ℝ) (981539362859/1000000000000 : ℝ) (38252047871/200000000000 : ℝ) (191260239361/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2137/16384 : ℝ)) (490769681429/500000000000 : ℝ) (981539362859/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2137/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490769681429/500000000000 : ℝ) (981539362859/1000000000000 : ℝ) (990769681429/1000000000000 : ℝ) (99076968143/100000000000 : ℝ) (247681671059/250000000000 : ℝ) (990726684237/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2137/16384 : ℝ)) 1 (990769681429/1000000000000 : ℝ) (99076968143/100000000000 : ℝ) (247681671059/250000000000 : ℝ) (990726684237/1000000000000 : ℝ) (61921761427/62500000000 : ℝ) (495374091417/500000000000 : ℝ) (990748182599/1000000000000 : ℝ) (990748182601/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2137/16384 : ℝ)) 2 (61921761427/62500000000 : ℝ) (495374091417/500000000000 : ℝ) (990748182599/1000000000000 : ℝ) (990748182601/1000000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2137/16384 : ℝ)) 3 (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2137/16384 : ℝ)) 4 (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2137/16384 : ℝ)) 5 (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2137/16384 : ℝ)) 6 (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2137/16384 : ℝ)) 7 (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2137/16384 : ℝ))) (38252047871/200000000000 : ℝ) (191260239361/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2137/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38252047871/200000000000 : ℝ) (191260239361/1000000000000 : ℝ) (595630119677/1000000000000 : ℝ) (595630119681/1000000000000 : ℝ) (54666637357/125000000000 : ℝ) (437333098863/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2137/16384 : ℝ))) 1 (595630119677/1000000000000 : ℝ) (595630119681/1000000000000 : ℝ) (54666637357/125000000000 : ℝ) (437333098863/1000000000000 : ℝ) (258240804633/500000000000 : ℝ) (64560201159/125000000000 : ℝ) (3987351569/7812500000 : ℝ) (255190500419/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2137/16384 : ℝ))) 2 (258240804633/500000000000 : ℝ) (64560201159/125000000000 : ℝ) (3987351569/7812500000 : ℝ) (255190500419/500000000000 : ℝ) (513431305049/1000000000000 : ℝ) (102686261011/200000000000 : ℝ) (256711122007/500000000000 : ℝ) (513422244021/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2137/16384 : ℝ))) 3 (513431305049/1000000000000 : ℝ) (102686261011/200000000000 : ℝ) (256711122007/500000000000 : ℝ) (513422244021/1000000000000 : ℝ) (513426774531/1000000000000 : ℝ) (256713387269/500000000000 : ℝ) (513426774511/1000000000000 : ℝ) (513426774519/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2137/16384 : ℝ))) 4 (513426774531/1000000000000 : ℝ) (256713387269/500000000000 : ℝ) (513426774511/1000000000000 : ℝ) (513426774519/1000000000000 : ℝ) (513426774521/1000000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2137/16384 : ℝ))) 5 (513426774521/1000000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2137/16384 : ℝ))) 6 (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2137/16384 : ℝ))) 7 (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2137/16384 : ℝ)) hmem 8 (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2137/16384 : ℝ))) hcmem 8 (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2137/16384 : ℝ)) (198149636543/200000000000 : ℝ) (495374091359/500000000000 : ℝ) (12835669363/25000000000 : ℝ) (513426774529/1000000000000 : ℝ) (814020056319/1000000000000 : ℝ) (50876253521/62500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0086_exp_lower
  have heNumeric : (1009543469201/500000000000 : ℝ)/4 ≤ Real.exp (-341824481293/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009543469201/500000000000 : ℝ)/4 ≤ Real.exp ((267/2048 : ℝ)-(50876253521/62500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (267/2048 : ℝ) (2137/16384 : ℝ) (50876253521/62500000000 : ℝ) (1009543469201/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0087; no trusted numerical premise.
theorem cover7_leaf0087_exp_radius : (249418119454392247/250000000000000000 : ℝ) ≤ Real.exp ((-1069/57344 : ℝ)/8) ∧ Real.exp ((-1069/57344 : ℝ)/8) ≤ (997672477817568989/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1069/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0087_exp_lower : (918093222588564453/1000000000000000000 : ℝ) ≤ Real.exp ((-546920600683/800000000000 : ℝ)/8) ∧ Real.exp ((-546920600683/800000000000 : ℝ)/8) ≤ (459046611294282227/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546920600683/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0087_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009541663869/500000000000 : ℝ) ≤ 4*Real.exp (2137/16384 : ℝ)*Real.exp (-mu (radius 7 (1069/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (1009541663869/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1069/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0087_exp_radius
  have hrNumeric : (981530804551/1000000000000 : ℝ) ≤ Real.exp (-1069/57344 : ℝ) ∧ Real.exp (-1069/57344 : ℝ) ≤ (122691350569/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981530804551/1000000000000 : ℝ) ≤ (radius 7 (1069/8192 : ℝ)) ∧ (radius 7 (1069/8192 : ℝ)) ≤ (122691350569/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1069/8192 : ℝ)) (981530804551/1000000000000 : ℝ) (122691350569/125000000000 : ℝ) (191304154987/1000000000000 : ℝ) (191304154993/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1069/8192 : ℝ)) (981530804551/1000000000000 : ℝ) (122691350569/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1069/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981530804551/1000000000000 : ℝ) (122691350569/125000000000 : ℝ) (39630616091/40000000000 : ℝ) (247691350569/250000000000 : ℝ) (49536118251/50000000000 : ℝ) (990722365021/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1069/8192 : ℝ)) 1 (39630616091/40000000000 : ℝ) (247691350569/250000000000 : ℝ) (49536118251/50000000000 : ℝ) (990722365021/1000000000000 : ℝ) (990743883647/1000000000000 : ℝ) (990743883649/1000000000000 : ℝ) (990743883413/1000000000000 : ℝ) (198148776683/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1069/8192 : ℝ)) 2 (990743883647/1000000000000 : ℝ) (990743883649/1000000000000 : ℝ) (990743883413/1000000000000 : ℝ) (198148776683/200000000000 : ℝ) (99074388353/100000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1069/8192 : ℝ)) 3 (99074388353/100000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1069/8192 : ℝ)) 4 (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1069/8192 : ℝ)) 5 (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1069/8192 : ℝ)) 6 (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1069/8192 : ℝ)) 7 (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1069/8192 : ℝ))) (191304154987/1000000000000 : ℝ) (191304154993/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1069/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191304154987/1000000000000 : ℝ) (191304154993/1000000000000 : ℝ) (595652077493/1000000000000 : ℝ) (595652077497/1000000000000 : ℝ) (437383304421/1000000000000 : ℝ) (437383304429/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1069/8192 : ℝ))) 1 (595652077493/1000000000000 : ℝ) (595652077497/1000000000000 : ℝ) (437383304421/1000000000000 : ℝ) (437383304429/1000000000000 : ℝ) (516517690957/1000000000000 : ℝ) (516517690963/1000000000000 : ℝ) (510419703713/1000000000000 : ℝ) (510419703721/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1069/8192 : ℝ))) 2 (516517690957/1000000000000 : ℝ) (516517690963/1000000000000 : ℝ) (510419703713/1000000000000 : ℝ) (510419703721/1000000000000 : ℝ) (102693739467/200000000000 : ℝ) (256734348671/500000000000 : ℝ) (64182455593/125000000000 : ℝ) (32091227797/62500000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1069/8192 : ℝ))) 3 (102693739467/200000000000 : ℝ) (256734348671/500000000000 : ℝ) (64182455593/125000000000 : ℝ) (32091227797/62500000000 : ℝ) (513464171039/1000000000000 : ℝ) (513464171047/1000000000000 : ℝ) (513464171019/1000000000000 : ℝ) (128366042757/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1069/8192 : ℝ))) 4 (513464171039/1000000000000 : ℝ) (513464171047/1000000000000 : ℝ) (513464171019/1000000000000 : ℝ) (128366042757/250000000000 : ℝ) (513464171029/1000000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1069/8192 : ℝ))) 5 (513464171029/1000000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1069/8192 : ℝ))) 6 (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1069/8192 : ℝ))) 7 (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1069/8192 : ℝ)) hmem 8 (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1069/8192 : ℝ))) hcmem 8 (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1069/8192 : ℝ)) (990743883529/1000000000000 : ℝ) (247685970883/250000000000 : ℝ) (128366042757/250000000000 : ℝ) (256732085519/500000000000 : ℝ) (814082879741/1000000000000 : ℝ) (10176035997/12500000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0087_exp_lower
  have heNumeric : (1009541663869/500000000000 : ℝ)/4 ≤ Real.exp (-546920600683/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009541663869/500000000000 : ℝ)/4 ≤ Real.exp ((2137/16384 : ℝ)-(10176035997/12500000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2137/16384 : ℝ) (1069/8192 : ℝ) (10176035997/12500000000 : ℝ) (1009541663869/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0088; no trusted numerical premise.
theorem cover7_leaf0088_exp_radius : (199534278088290991/200000000000000000 : ℝ) ≤ Real.exp ((-2139/114688 : ℝ)/8) ∧ Real.exp ((-2139/114688 : ℝ)/8) ≤ (249417847610363739/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2139/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0088_exp_lower : (459046509811955337/500000000000000000 : ℝ) ≤ Real.exp ((-1367305038859/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367305038859/2000000000000 : ℝ)/8) ≤ (36723720784956427/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367305038859/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0088_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019079756839/1000000000000 : ℝ) ≤ 4*Real.exp (1069/8192 : ℝ)*Real.exp (-mu (radius 7 (2139/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019079756839/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2139/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0088_exp_radius
  have hrNumeric : (981522246319/1000000000000 : ℝ) ≤ Real.exp (-2139/114688 : ℝ) ∧ Real.exp (-2139/114688 : ℝ) ≤ (12269028079/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981522246319/1000000000000 : ℝ) ≤ (radius 7 (2139/16384 : ℝ)) ∧ (radius 7 (2139/16384 : ℝ)) ≤ (12269028079/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2139/16384 : ℝ)) (981522246319/1000000000000 : ℝ) (12269028079/12500000000 : ℝ) (191348059773/1000000000000 : ℝ) (191348059779/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2139/16384 : ℝ)) (981522246319/1000000000000 : ℝ) (12269028079/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2139/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981522246319/1000000000000 : ℝ) (12269028079/12500000000 : ℝ) (990761123159/1000000000000 : ℝ) (24769028079/25000000000 : ℝ) (495359022911/500000000000 : ℝ) (7739984733/7812500000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2139/16384 : ℝ)) 1 (990761123159/1000000000000 : ℝ) (24769028079/25000000000 : ℝ) (495359022911/500000000000 : ℝ) (7739984733/7812500000 : ℝ) (99073958449/100000000000 : ℝ) (247684896123/250000000000 : ℝ) (3870076501/3906250000 : ℝ) (495369792129/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2139/16384 : ℝ)) 2 (99073958449/100000000000 : ℝ) (247684896123/250000000000 : ℝ) (3870076501/3906250000 : ℝ) (495369792129/500000000000 : ℝ) (990739584373/1000000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2139/16384 : ℝ)) 3 (990739584373/1000000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2139/16384 : ℝ)) 4 (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2139/16384 : ℝ)) 5 (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2139/16384 : ℝ)) 6 (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2139/16384 : ℝ)) 7 (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2139/16384 : ℝ))) (191348059773/1000000000000 : ℝ) (191348059779/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2139/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191348059773/1000000000000 : ℝ) (191348059779/1000000000000 : ℝ) (297837014943/500000000000 : ℝ) (59567402989/100000000000 : ℝ) (109358372957/250000000000 : ℝ) (109358372959/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2139/16384 : ℝ))) 1 (297837014943/500000000000 : ℝ) (59567402989/100000000000 : ℝ) (109358372957/250000000000 : ℝ) (109358372959/250000000000 : ℝ) (516553760857/1000000000000 : ℝ) (516553760863/1000000000000 : ℝ) (255229196451/500000000000 : ℝ) (510458392909/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2139/16384 : ℝ))) 2 (516553760857/1000000000000 : ℝ) (516553760863/1000000000000 : ℝ) (255229196451/500000000000 : ℝ) (510458392909/1000000000000 : ℝ) (513506076879/1000000000000 : ℝ) (256753038443/500000000000 : ℝ) (256748516361/500000000000 : ℝ) (513497032729/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2139/16384 : ℝ))) 3 (513506076879/1000000000000 : ℝ) (256753038443/500000000000 : ℝ) (256748516361/500000000000 : ℝ) (513497032729/1000000000000 : ℝ) (1283753887/2500000000 : ℝ) (64187694351/125000000000 : ℝ) (25675077739/50000000000 : ℝ) (128375388697/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2139/16384 : ℝ))) 4 (1283753887/2500000000 : ℝ) (64187694351/125000000000 : ℝ) (25675077739/50000000000 : ℝ) (128375388697/250000000000 : ℝ) (51350155479/100000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2139/16384 : ℝ))) 5 (51350155479/100000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2139/16384 : ℝ))) 6 (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2139/16384 : ℝ))) 7 (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2139/16384 : ℝ)) hmem 8 (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2139/16384 : ℝ))) hcmem 8 (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2139/16384 : ℝ)) (247684896093/250000000000 : ℝ) (317036667/320000000 : ℝ) (513501554789/1000000000000 : ℝ) (256750777399/500000000000 : ℝ) (407072841737/500000000000 : ℝ) (203536420873/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0088_exp_lower
  have heNumeric : (2019079756839/1000000000000 : ℝ)/4 ≤ Real.exp (-1367305038859/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019079756839/1000000000000 : ℝ)/4 ≤ Real.exp ((1069/8192 : ℝ)-(203536420873/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1069/8192 : ℝ) (2139/16384 : ℝ) (203536420873/250000000000 : ℝ) (2019079756839/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0089; no trusted numerical premise.
theorem cover7_leaf0089_exp_radius : (249417575766631517/250000000000000000 : ℝ) ≤ Real.exp ((-535/28672 : ℝ)/8) ∧ Real.exp ((-535/28672 : ℝ)/8) ≤ (997670303066526069/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-535/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0089_exp_lower : (918092818917236289/1000000000000000000 : ℝ) ≤ Real.exp ((-2734617073321/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734617073321/4000000000000 : ℝ)/8) ≤ (91809281891723629/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734617073321/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0089_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252384528209/125000000000 : ℝ) ≤ 4*Real.exp (2139/16384 : ℝ)*Real.exp (-mu (radius 7 (535/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (252384528209/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (535/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0089_exp_radius
  have hrNumeric : (490756844081/500000000000 : ℝ) ≤ Real.exp (-535/28672 : ℝ) ∧ Real.exp (-535/28672 : ℝ) ≤ (981513688163/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490756844081/500000000000 : ℝ) ≤ (radius 7 (535/4096 : ℝ)) ∧ (radius 7 (535/4096 : ℝ)) ≤ (981513688163/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (535/4096 : ℝ)) (490756844081/500000000000 : ℝ) (981513688163/1000000000000 : ℝ) (191391953719/1000000000000 : ℝ) (7655678149/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (535/4096 : ℝ)) (490756844081/500000000000 : ℝ) (981513688163/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (535/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490756844081/500000000000 : ℝ) (981513688163/1000000000000 : ℝ) (990756844081/1000000000000 : ℝ) (495378422041/500000000000 : ℝ) (247678431661/250000000000 : ℝ) (495356863323/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (535/4096 : ℝ)) 1 (990756844081/1000000000000 : ℝ) (495378422041/500000000000 : ℝ) (247678431661/250000000000 : ℝ) (495356863323/500000000000 : ℝ) (495367642681/500000000000 : ℝ) (247683821341/250000000000 : ℝ) (990735285127/1000000000000 : ℝ) (99073528513/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (535/4096 : ℝ)) 2 (495367642681/500000000000 : ℝ) (247683821341/250000000000 : ℝ) (990735285127/1000000000000 : ℝ) (99073528513/100000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (535/4096 : ℝ)) 3 (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (535/4096 : ℝ)) 4 (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (535/4096 : ℝ)) 5 (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (535/4096 : ℝ)) 6 (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (535/4096 : ℝ)) 7 (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (535/4096 : ℝ))) (191391953719/1000000000000 : ℝ) (7655678149/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (535/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191391953719/1000000000000 : ℝ) (7655678149/40000000000 : ℝ) (595695976859/1000000000000 : ℝ) (595695976863/1000000000000 : ℝ) (13671364409/31250000000 : ℝ) (87496732219/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (535/4096 : ℝ))) 1 (595695976859/1000000000000 : ℝ) (595695976863/1000000000000 : ℝ) (13671364409/31250000000 : ℝ) (87496732219/200000000000 : ℝ) (516589818973/1000000000000 : ℝ) (516589818979/1000000000000 : ℝ) (255248534203/500000000000 : ℝ) (510497068413/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (535/4096 : ℝ))) 2 (516589818973/1000000000000 : ℝ) (516589818979/1000000000000 : ℝ) (255248534203/500000000000 : ℝ) (510497068413/1000000000000 : ℝ) (513543443689/1000000000000 : ℝ) (32096465231/62500000000 : ℝ) (102706881591/200000000000 : ℝ) (256767203981/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (535/4096 : ℝ))) 3 (513543443689/1000000000000 : ℝ) (32096465231/62500000000 : ℝ) (102706881591/200000000000 : ℝ) (256767203981/500000000000 : ℝ) (256769462911/500000000000 : ℝ) (513538925829/1000000000000 : ℝ) (256769462901/500000000000 : ℝ) (51353892581/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (535/4096 : ℝ))) 4 (256769462911/500000000000 : ℝ) (513538925829/1000000000000 : ℝ) (256769462901/500000000000 : ℝ) (51353892581/100000000000 : ℝ) (128384731453/250000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (535/4096 : ℝ))) 5 (128384731453/250000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (535/4096 : ℝ))) 6 (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (535/4096 : ℝ))) 7 (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (535/4096 : ℝ)) hmem 8 (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (535/4096 : ℝ))) hcmem 8 (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (535/4096 : ℝ)) (247683821311/250000000000 : ℝ) (990735285247/1000000000000 : ℝ) (513538925811/1000000000000 : ℝ) (25676946291/50000000000 : ℝ) (814208467531/1000000000000 : ℝ) (814208467549/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0089_exp_lower
  have heNumeric : (252384528209/125000000000 : ℝ)/4 ≤ Real.exp (-2734617073321/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252384528209/125000000000 : ℝ)/4 ≤ Real.exp ((2139/16384 : ℝ)-(814208467549/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2139/16384 : ℝ) (535/4096 : ℝ) (814208467549/1000000000000 : ℝ) (252384528209/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0090; no trusted numerical premise.
theorem cover7_leaf0090_exp_radius : (39906768627711293/40000000000000000 : ℝ) ≤ Real.exp ((-2141/114688 : ℝ)/8) ∧ Real.exp ((-2141/114688 : ℝ)/8) ≤ (498834607846391163/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2141/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0090_exp_lower : (459046310232720627/500000000000000000 : ℝ) ≤ Real.exp ((-683655997583/1000000000000 : ℝ)/8) ∧ Real.exp ((-683655997583/1000000000000 : ℝ)/8) ≤ (183618524093088251/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683655997583/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0090_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009536367091/500000000000 : ℝ) ≤ 4*Real.exp (535/4096 : ℝ)*Real.exp (-mu (radius 7 (2141/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009536367091/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2141/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0090_exp_radius
  have hrNumeric : (981505130079/1000000000000 : ℝ) ≤ Real.exp (-2141/114688 : ℝ) ∧ Real.exp (-2141/114688 : ℝ) ≤ (6134407063/6250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981505130079/1000000000000 : ℝ) ≤ (radius 7 (2141/16384 : ℝ)) ∧ (radius 7 (2141/16384 : ℝ)) ≤ (6134407063/6250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2141/16384 : ℝ)) (981505130079/1000000000000 : ℝ) (6134407063/6250000000 : ℝ) (4785895921/25000000000 : ℝ) (95717918423/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2141/16384 : ℝ)) (981505130079/1000000000000 : ℝ) (6134407063/6250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2141/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981505130079/1000000000000 : ℝ) (6134407063/6250000000 : ℝ) (990752565039/1000000000000 : ℝ) (12384407063/12500000000 : ℝ) (247677351871/250000000000 : ℝ) (495354703743/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2141/16384 : ℝ)) 1 (990752565039/1000000000000 : ℝ) (12384407063/12500000000 : ℝ) (247677351871/250000000000 : ℝ) (495354703743/500000000000 : ℝ) (990730986261/1000000000000 : ℝ) (990730986263/1000000000000 : ℝ) (495365493013/500000000000 : ℝ) (247682746507/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2141/16384 : ℝ)) 2 (990730986261/1000000000000 : ℝ) (990730986263/1000000000000 : ℝ) (495365493013/500000000000 : ℝ) (247682746507/250000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2141/16384 : ℝ)) 3 (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2141/16384 : ℝ)) 4 (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2141/16384 : ℝ)) 5 (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2141/16384 : ℝ)) 6 (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2141/16384 : ℝ)) 7 (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2141/16384 : ℝ))) (4785895921/25000000000 : ℝ) (95717918423/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2141/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (4785895921/25000000000 : ℝ) (95717918423/500000000000 : ℝ) (29785895921/50000000000 : ℝ) (595717918423/1000000000000 : ℝ) (854558227/1953125000 : ℝ) (54691726529/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2141/16384 : ℝ))) 1 (29785895921/50000000000 : ℝ) (595717918423/1000000000000 : ℝ) (854558227/1953125000 : ℝ) (54691726529/125000000000 : ℝ) (258312932661/500000000000 : ℝ) (32289116583/62500000000 : ℝ) (127633932561/250000000000 : ℝ) (510535730251/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2141/16384 : ℝ))) 2 (258312932661/500000000000 : ℝ) (32289116583/62500000000 : ℝ) (127633932561/250000000000 : ℝ) (510535730251/1000000000000 : ℝ) (513580797783/1000000000000 : ℝ) (51358079779/100000000000 : ℝ) (513571770461/1000000000000 : ℝ) (513571770469/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2141/16384 : ℝ))) 3 (513580797783/1000000000000 : ℝ) (51358079779/100000000000 : ℝ) (513571770461/1000000000000 : ℝ) (513571770469/1000000000000 : ℝ) (256788142061/500000000000 : ℝ) (51357628413/100000000000 : ℝ) (256788142051/500000000000 : ℝ) (51357628411/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2141/16384 : ℝ))) 4 (256788142061/500000000000 : ℝ) (51357628413/100000000000 : ℝ) (256788142051/500000000000 : ℝ) (51357628411/100000000000 : ℝ) (32098517757/62500000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2141/16384 : ℝ))) 5 (32098517757/62500000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2141/16384 : ℝ))) 6 (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2141/16384 : ℝ))) 7 (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2141/16384 : ℝ)) hmem 8 (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2141/16384 : ℝ))) hcmem 8 (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2141/16384 : ℝ)) (990730986143/1000000000000 : ℝ) (495365493073/500000000000 : ℝ) (513576284111/1000000000000 : ℝ) (12839407103/25000000000 : ℝ) (40713561597/50000000000 : ℝ) (407135615979/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0090_exp_lower
  have heNumeric : (1009536367091/500000000000 : ℝ)/4 ≤ Real.exp (-683655997583/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009536367091/500000000000 : ℝ)/4 ≤ Real.exp ((535/4096 : ℝ)-(407135615979/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (535/4096 : ℝ) (2141/16384 : ℝ) (407135615979/500000000000 : ℝ) (1009536367091/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0091; no trusted numerical premise.
theorem cover7_leaf0091_exp_radius : (249417032080055931/250000000000000000 : ℝ) ≤ Real.exp ((-153/8192 : ℝ)/8) ∧ Real.exp ((-153/8192 : ℝ)/8) ≤ (39906725132808949/40000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-153/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0091_exp_lower : (114761553033536823/125000000000000000 : ℝ) ≤ Real.exp ((-2734630828759/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734630828759/4000000000000 : ℝ)/8) ≤ (183618484853658917/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734630828759/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0091_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (504767320591/250000000000 : ℝ) ≤ 4*Real.exp (2141/16384 : ℝ)*Real.exp (-mu (radius 7 (1071/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (504767320591/250000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1071/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0091_exp_radius
  have hrNumeric : (981496572071/1000000000000 : ℝ) ≤ Real.exp (-153/8192 : ℝ) ∧ Real.exp (-153/8192 : ℝ) ≤ (122687071509/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981496572071/1000000000000 : ℝ) ≤ (radius 7 (1071/8192 : ℝ)) ∧ (radius 7 (1071/8192 : ℝ)) ≤ (122687071509/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1071/8192 : ℝ)) (981496572071/1000000000000 : ℝ) (122687071509/125000000000 : ℝ) (11967481821/62500000000 : ℝ) (95739854571/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1071/8192 : ℝ)) (981496572071/1000000000000 : ℝ) (122687071509/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1071/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981496572071/1000000000000 : ℝ) (122687071509/125000000000 : ℝ) (198149657207/200000000000 : ℝ) (247687071509/250000000000 : ℝ) (123838136043/125000000000 : ℝ) (198141017669/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1071/8192 : ℝ)) 1 (198149657207/200000000000 : ℝ) (247687071509/250000000000 : ℝ) (123838136043/125000000000 : ℝ) (198141017669/200000000000 : ℝ) (990726687189/1000000000000 : ℝ) (990726687191/1000000000000 : ℝ) (495363343477/500000000000 : ℝ) (247681671739/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1071/8192 : ℝ)) 2 (990726687189/1000000000000 : ℝ) (990726687191/1000000000000 : ℝ) (495363343477/500000000000 : ℝ) (247681671739/250000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1071/8192 : ℝ)) 3 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1071/8192 : ℝ)) 4 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1071/8192 : ℝ)) 5 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1071/8192 : ℝ)) 6 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1071/8192 : ℝ)) 7 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1071/8192 : ℝ))) (11967481821/62500000000 : ℝ) (95739854571/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1071/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11967481821/62500000000 : ℝ) (95739854571/500000000000 : ℝ) (74467481821/125000000000 : ℝ) (595739854571/1000000000000 : ℝ) (109395986311/250000000000 : ℝ) (109395986313/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1071/8192 : ℝ))) 1 (74467481821/125000000000 : ℝ) (595739854571/1000000000000 : ℝ) (109395986311/250000000000 : ℝ) (109395986313/250000000000 : ℝ) (258330949953/500000000000 : ℝ) (64582737489/125000000000 : ℝ) (510574378421/1000000000000 : ℝ) (127643594607/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1071/8192 : ℝ))) 2 (258330949953/500000000000 : ℝ) (64582737489/125000000000 : ℝ) (510574378421/1000000000000 : ℝ) (127643594607/250000000000 : ℝ) (513618139163/1000000000000 : ℝ) (51361813917/100000000000 : ℝ) (128402280061/250000000000 : ℝ) (513609120251/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1071/8192 : ℝ))) 3 (513618139163/1000000000000 : ℝ) (51361813917/100000000000 : ℝ) (128402280061/250000000000 : ℝ) (513609120251/1000000000000 : ℝ) (513613629703/1000000000000 : ℝ) (513613629711/1000000000000 : ℝ) (513613629683/1000000000000 : ℝ) (513613629691/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1071/8192 : ℝ))) 4 (513613629703/1000000000000 : ℝ) (513613629711/1000000000000 : ℝ) (513613629683/1000000000000 : ℝ) (513613629691/1000000000000 : ℝ) (513613629693/1000000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1071/8192 : ℝ))) 5 (513613629693/1000000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1071/8192 : ℝ))) 6 (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1071/8192 : ℝ))) 7 (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1071/8192 : ℝ)) hmem 8 (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1071/8192 : ℝ))) hcmem 8 (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1071/8192 : ℝ)) (990726687071/1000000000000 : ℝ) (495363343537/500000000000 : ℝ) (128403407423/250000000000 : ℝ) (513613629701/1000000000000 : ℝ) (6361984193/7812500000 : ℝ) (814333976721/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0091_exp_lower
  have heNumeric : (504767320591/250000000000 : ℝ)/4 ≤ Real.exp (-2734630828759/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (504767320591/250000000000 : ℝ)/4 ≤ Real.exp ((2141/16384 : ℝ)-(814333976721/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2141/16384 : ℝ) (1071/8192 : ℝ) (814333976721/1000000000000 : ℝ) (504767320591/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0092; no trusted numerical premise.
theorem cover7_leaf0092_exp_radius : (124708380118606283/125000000000000000 : ℝ) ≤ Real.exp ((-2143/114688 : ℝ)/8) ∧ Real.exp ((-2143/114688 : ℝ)/8) ≤ (199533408189770053/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2143/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0092_exp_lower : (459046115161003851/500000000000000000 : ℝ) ≤ Real.exp ((-1367318794367/2000000000000 : ℝ)/8) ∧ Real.exp ((-1367318794367/2000000000000 : ℝ)/8) ≤ (918092230322007703/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1367318794367/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0092_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019065870153/1000000000000 : ℝ) ≤ 4*Real.exp (1071/8192 : ℝ)*Real.exp (-mu (radius 7 (2143/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019065870153/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2143/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0092_exp_radius
  have hrNumeric : (981488014137/1000000000000 : ℝ) ≤ Real.exp (-2143/114688 : ℝ) ∧ Real.exp (-2143/114688 : ℝ) ≤ (490744007069/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981488014137/1000000000000 : ℝ) ≤ (radius 7 (2143/16384 : ℝ)) ∧ (radius 7 (2143/16384 : ℝ)) ≤ (490744007069/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2143/16384 : ℝ)) (981488014137/1000000000000 : ℝ) (490744007069/500000000000 : ℝ) (191523570621/1000000000000 : ℝ) (191523570627/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2143/16384 : ℝ)) (981488014137/1000000000000 : ℝ) (490744007069/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2143/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981488014137/1000000000000 : ℝ) (490744007069/500000000000 : ℝ) (247686001767/250000000000 : ℝ) (990744007069/1000000000000 : ℝ) (990700769221/1000000000000 : ℝ) (990700769223/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2143/16384 : ℝ)) 1 (247686001767/250000000000 : ℝ) (990744007069/1000000000000 : ℝ) (990700769221/1000000000000 : ℝ) (990700769223/1000000000000 : ℝ) (61920149259/62500000000 : ℝ) (495361194073/500000000000 : ℝ) (247680596977/250000000000 : ℝ) (990722387911/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2143/16384 : ℝ)) 2 (61920149259/62500000000 : ℝ) (495361194073/500000000000 : ℝ) (247680596977/250000000000 : ℝ) (990722387911/1000000000000 : ℝ) (495361194013/500000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2143/16384 : ℝ)) 3 (495361194013/500000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2143/16384 : ℝ)) 4 (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2143/16384 : ℝ)) 5 (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2143/16384 : ℝ)) 6 (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2143/16384 : ℝ)) 7 (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2143/16384 : ℝ))) (191523570621/1000000000000 : ℝ) (191523570627/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2143/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191523570621/1000000000000 : ℝ) (191523570627/1000000000000 : ℝ) (59576178531/100000000000 : ℝ) (297880892657/500000000000 : ℝ) (43763406017/100000000000 : ℝ) (437634060177/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2143/16384 : ℝ))) 1 (59576178531/100000000000 : ℝ) (297880892657/500000000000 : ℝ) (43763406017/100000000000 : ℝ) (437634060177/1000000000000 : ℝ) (25834896137/50000000000 : ℝ) (258348961373/500000000000 : ℝ) (102122602591/200000000000 : ℝ) (255306506481/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2143/16384 : ℝ))) 2 (25834896137/50000000000 : ℝ) (258348961373/500000000000 : ℝ) (102122602591/200000000000 : ℝ) (255306506481/500000000000 : ℝ) (513655467847/1000000000000 : ℝ) (256827733927/500000000000 : ℝ) (12841161433/25000000000 : ℝ) (513646457327/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2143/16384 : ℝ))) 3 (513655467847/1000000000000 : ℝ) (256827733927/500000000000 : ℝ) (12841161433/25000000000 : ℝ) (513646457327/1000000000000 : ℝ) (513650962583/1000000000000 : ℝ) (513650962591/1000000000000 : ℝ) (513650962563/1000000000000 : ℝ) (513650962571/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2143/16384 : ℝ))) 4 (513650962583/1000000000000 : ℝ) (513650962591/1000000000000 : ℝ) (513650962563/1000000000000 : ℝ) (513650962571/1000000000000 : ℝ) (513650962573/1000000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2143/16384 : ℝ))) 5 (513650962573/1000000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2143/16384 : ℝ))) 6 (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2143/16384 : ℝ))) 7 (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2143/16384 : ℝ)) hmem 8 (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2143/16384 : ℝ))) hcmem 8 (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2143/16384 : ℝ)) (39628895521/40000000000 : ℝ) (990722388029/1000000000000 : ℝ) (128412740643/250000000000 : ℝ) (513650962581/1000000000000 : ℝ) (814396701853/1000000000000 : ℝ) (814396701871/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0092_exp_lower
  have heNumeric : (2019065870153/1000000000000 : ℝ)/4 ≤ Real.exp (-1367318794367/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019065870153/1000000000000 : ℝ)/4 ≤ Real.exp ((1071/8192 : ℝ)-(814396701871/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1071/8192 : ℝ) (2143/16384 : ℝ) (814396701871/1000000000000 : ℝ) (2019065870153/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0093; no trusted numerical premise.
theorem cover7_leaf0093_exp_radius : (199533190715732389/200000000000000000 : ℝ) ≤ Real.exp ((-67/3584 : ℝ)/8) ∧ Real.exp ((-67/3584 : ℝ)/8) ≤ (498832976789330973/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-67/3584 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0093_exp_lower : (459046019313232211/500000000000000000 : ℝ) ≤ Real.exp ((-2734644270261/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734644270261/4000000000000 : ℝ)/8) ≤ (918092038626464423/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734644270261/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0093_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403812499509/200000000000 : ℝ) ≤ 4*Real.exp (2143/16384 : ℝ)*Real.exp (-mu (radius 7 (67/512 : ℝ))) ∧ (2019/1000 : ℝ) < (403812499509/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (67/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0093_exp_radius
  have hrNumeric : (490739728139/500000000000 : ℝ) ≤ Real.exp (-67/3584 : ℝ) ∧ Real.exp (-67/3584 : ℝ) ≤ (981479456279/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490739728139/500000000000 : ℝ) ≤ (radius 7 (67/512 : ℝ)) ∧ (radius 7 (67/512 : ℝ)) ≤ (981479456279/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (67/512 : ℝ)) (490739728139/500000000000 : ℝ) (981479456279/1000000000000 : ℝ) (11972963831/62500000000 : ℝ) (95783710651/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (67/512 : ℝ)) (490739728139/500000000000 : ℝ) (981479456279/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (67/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490739728139/500000000000 : ℝ) (981479456279/1000000000000 : ℝ) (990739728139/1000000000000 : ℝ) (49536986407/50000000000 : ℝ) (495348225059/500000000000 : ℝ) (24767411253/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (67/512 : ℝ)) 1 (990739728139/1000000000000 : ℝ) (49536986407/50000000000 : ℝ) (495348225059/500000000000 : ℝ) (24767411253/25000000000 : ℝ) (123839761141/125000000000 : ℝ) (99071808913/100000000000 : ℝ) (247679522223/250000000000 : ℝ) (495359044447/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (67/512 : ℝ)) 2 (123839761141/125000000000 : ℝ) (99071808913/100000000000 : ℝ) (247679522223/250000000000 : ℝ) (495359044447/500000000000 : ℝ) (99071808901/100000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (67/512 : ℝ)) 3 (99071808901/100000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (67/512 : ℝ)) 4 (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (67/512 : ℝ)) 5 (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (67/512 : ℝ)) 6 (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (67/512 : ℝ)) 7 (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (67/512 : ℝ))) (11972963831/62500000000 : ℝ) (95783710651/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (67/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (11972963831/62500000000 : ℝ) (95783710651/500000000000 : ℝ) (74472963831/125000000000 : ℝ) (595783710651/1000000000000 : ℝ) (27355259813/62500000000 : ℝ) (54710519627/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (67/512 : ℝ))) 1 (74472963831/125000000000 : ℝ) (595783710651/1000000000000 : ℝ) (27355259813/62500000000 : ℝ) (54710519627/125000000000 : ℝ) (129183483457/250000000000 : ℝ) (258366966917/500000000000 : ℝ) (10213032677/20000000000 : ℝ) (510651633857/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (67/512 : ℝ))) 2 (129183483457/250000000000 : ℝ) (258366966917/500000000000 : ℝ) (10213032677/20000000000 : ℝ) (510651633857/1000000000000 : ℝ) (513692783839/1000000000000 : ℝ) (256846391923/500000000000 : ℝ) (513683781693/1000000000000 : ℝ) (513683781701/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (67/512 : ℝ))) 3 (513692783839/1000000000000 : ℝ) (256846391923/500000000000 : ℝ) (513683781693/1000000000000 : ℝ) (513683781701/1000000000000 : ℝ) (256844141383/500000000000 : ℝ) (256844141387/500000000000 : ℝ) (256844141373/500000000000 : ℝ) (256844141377/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (67/512 : ℝ))) 4 (256844141383/500000000000 : ℝ) (256844141387/500000000000 : ℝ) (256844141373/500000000000 : ℝ) (256844141377/500000000000 : ℝ) (128422070689/250000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (67/512 : ℝ))) 5 (128422070689/250000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (67/512 : ℝ))) 6 (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (67/512 : ℝ))) 7 (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (67/512 : ℝ)) hmem 8 (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (67/512 : ℝ))) hcmem 8 (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (67/512 : ℝ)) (990718089009/1000000000000 : ℝ) (247679522253/250000000000 : ℝ) (102737656551/200000000000 : ℝ) (128422070691/250000000000 : ℝ) (814459407391/1000000000000 : ℝ) (814459407409/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0093_exp_lower
  have heNumeric : (403812499509/200000000000 : ℝ)/4 ≤ Real.exp (-2734644270261/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403812499509/200000000000 : ℝ)/4 ≤ Real.exp ((2143/16384 : ℝ)-(814459407409/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2143/16384 : ℝ) (67/512 : ℝ) (814459407409/1000000000000 : ℝ) (403812499509/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0094; no trusted numerical premise.
theorem cover7_leaf0094_exp_radius : (199532973241931753/200000000000000000 : ℝ) ≤ Real.exp ((-2145/114688 : ℝ)/8) ∧ Real.exp ((-2145/114688 : ℝ)/8) ≤ (498832433104829383/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2145/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0094_exp_lower : (459045924589798813/500000000000000000 : ℝ) ≤ Real.exp ((-683662718353/1000000000000 : ℝ)/8) ∧ Real.exp ((-683662718353/1000000000000 : ℝ)/8) ≤ (918091849179597627/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683662718353/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0094_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252382395563/125000000000 : ℝ) ≤ 4*Real.exp (67/512 : ℝ)*Real.exp (-mu (radius 7 (2145/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (252382395563/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2145/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0094_exp_radius
  have hrNumeric : (490735449247/500000000000 : ℝ) ≤ Real.exp (-2145/114688 : ℝ) ∧ Real.exp (-2145/114688 : ℝ) ≤ (196294179699/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490735449247/500000000000 : ℝ) ≤ (radius 7 (2145/16384 : ℝ)) ∧ (radius 7 (2145/16384 : ℝ)) ≤ (196294179699/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2145/16384 : ℝ)) (490735449247/500000000000 : ℝ) (196294179699/200000000000 : ℝ) (19161126117/100000000000 : ℝ) (23951407647/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2145/16384 : ℝ)) (490735449247/500000000000 : ℝ) (196294179699/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2145/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490735449247/500000000000 : ℝ) (196294179699/200000000000 : ℝ) (990735449247/1000000000000 : ℝ) (30960482789/31250000000 : ℝ) (495346065517/500000000000 : ℝ) (247673032759/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2145/16384 : ℝ)) 1 (990735449247/1000000000000 : ℝ) (30960482789/31250000000 : ℝ) (495346065517/500000000000 : ℝ) (247673032759/250000000000 : ℝ) (49535689507/50000000000 : ℝ) (495356895071/500000000000 : ℝ) (990713789903/1000000000000 : ℝ) (495356894953/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2145/16384 : ℝ)) 2 (49535689507/50000000000 : ℝ) (495356895071/500000000000 : ℝ) (990713789903/1000000000000 : ℝ) (495356894953/500000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2145/16384 : ℝ)) 3 (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2145/16384 : ℝ)) 4 (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2145/16384 : ℝ)) 5 (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2145/16384 : ℝ)) 6 (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2145/16384 : ℝ)) 7 (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2145/16384 : ℝ))) (19161126117/100000000000 : ℝ) (23951407647/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2145/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (19161126117/100000000000 : ℝ) (23951407647/125000000000 : ℝ) (119161126117/200000000000 : ℝ) (148951407647/250000000000 : ℝ) (17509369431/40000000000 : ℝ) (437734235783/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2145/16384 : ℝ))) 1 (119161126117/200000000000 : ℝ) (148951407647/250000000000 : ℝ) (17509369431/40000000000 : ℝ) (437734235783/1000000000000 : ℝ) (25838496659/50000000000 : ℝ) (258384966593/500000000000 : ℝ) (510690241119/1000000000000 : ℝ) (255345120563/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2145/16384 : ℝ))) 2 (25838496659/50000000000 : ℝ) (258384966593/500000000000 : ℝ) (510690241119/1000000000000 : ℝ) (255345120563/500000000000 : ℝ) (513730087149/1000000000000 : ℝ) (128432521789/250000000000 : ℝ) (4109768747/8000000000 : ℝ) (256860546691/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2145/16384 : ℝ))) 3 (513730087149/1000000000000 : ℝ) (128432521789/250000000000 : ℝ) (4109768747/8000000000 : ℝ) (256860546691/500000000000 : ℝ) (256862795131/500000000000 : ℝ) (513725590269/1000000000000 : ℝ) (256862795121/500000000000 : ℝ) (2054902361/4000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2145/16384 : ℝ))) 4 (256862795131/500000000000 : ℝ) (513725590269/1000000000000 : ℝ) (256862795121/500000000000 : ℝ) (2054902361/4000000000 : ℝ) (128431397563/250000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2145/16384 : ℝ))) 5 (128431397563/250000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2145/16384 : ℝ))) 6 (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2145/16384 : ℝ))) 7 (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2145/16384 : ℝ)) hmem 8 (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2145/16384 : ℝ))) hcmem 8 (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2145/16384 : ℝ)) (990713790021/1000000000000 : ℝ) (123839223753/125000000000 : ℝ) (513725590251/1000000000000 : ℝ) (25686279513/50000000000 : ℝ) (162904418667/200000000000 : ℝ) (814522093353/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0094_exp_lower
  have heNumeric : (252382395563/125000000000 : ℝ)/4 ≤ Real.exp (-683662718353/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252382395563/125000000000 : ℝ)/4 ≤ Real.exp ((67/512 : ℝ)-(814522093353/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (67/512 : ℝ) (2145/16384 : ℝ) (814522093353/1000000000000 : ℝ) (252382395563/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0095; no trusted numerical premise.
theorem cover7_leaf0095_exp_radius : (498831889420920361/500000000000000000 : ℝ) ≤ Real.exp ((-1073/57344 : ℝ)/8) ∧ Real.exp ((-1073/57344 : ℝ)/8) ≤ (997663778841840723/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1073/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0095_exp_lower : (114761457747345801/125000000000000000 : ℝ) ≤ Real.exp ((-2734657398279/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734657398279/4000000000000 : ℝ)/8) ≤ (918091661978766409/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734657398279/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0095_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (252381983873/125000000000 : ℝ) ≤ 4*Real.exp (2145/16384 : ℝ)*Real.exp (-mu (radius 7 (1073/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (252381983873/125000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1073/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0095_exp_radius
  have hrNumeric : (61341396299/62500000000 : ℝ) ≤ Real.exp (-1073/57344 : ℝ) ∧ Real.exp (-1073/57344 : ℝ) ≤ (196292468157/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61341396299/62500000000 : ℝ) ≤ (radius 7 (1073/8192 : ℝ)) ∧ (radius 7 (1073/8192 : ℝ)) ≤ (196292468157/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1073/8192 : ℝ)) (61341396299/62500000000 : ℝ) (196292468157/200000000000 : ℝ) (38331018051/200000000000 : ℝ) (191655090261/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1073/8192 : ℝ)) (61341396299/62500000000 : ℝ) (196292468157/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1073/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61341396299/62500000000 : ℝ) (196292468157/200000000000 : ℝ) (123841396299/125000000000 : ℝ) (990731170393/1000000000000 : ℝ) (990687811969/1000000000000 : ℝ) (99068781197/100000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1073/8192 : ℝ)) 1 (123841396299/125000000000 : ℝ) (990731170393/1000000000000 : ℝ) (990687811969/1000000000000 : ℝ) (99068781197/100000000000 : ℝ) (49535474559/50000000000 : ℝ) (495354745591/500000000000 : ℝ) (990709490943/1000000000000 : ℝ) (198141898189/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1073/8192 : ℝ)) 2 (49535474559/50000000000 : ℝ) (495354745591/500000000000 : ℝ) (990709490943/1000000000000 : ℝ) (198141898189/200000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1073/8192 : ℝ)) 3 (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1073/8192 : ℝ)) 4 (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1073/8192 : ℝ)) 5 (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1073/8192 : ℝ)) 6 (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1073/8192 : ℝ)) 7 (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1073/8192 : ℝ))) (38331018051/200000000000 : ℝ) (191655090261/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1073/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38331018051/200000000000 : ℝ) (191655090261/1000000000000 : ℝ) (595827545127/1000000000000 : ℝ) (595827545131/1000000000000 : ℝ) (109446074123/250000000000 : ℝ) (437784296499/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1073/8192 : ℝ))) 1 (595827545127/1000000000000 : ℝ) (595827545131/1000000000000 : ℝ) (109446074123/250000000000 : ℝ) (437784296499/1000000000000 : ℝ) (516805920809/1000000000000 : ℝ) (103361184163/200000000000 : ℝ) (255364417389/500000000000 : ℝ) (102145766957/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1073/8192 : ℝ))) 2 (516805920809/1000000000000 : ℝ) (103361184163/200000000000 : ℝ) (255364417389/500000000000 : ℝ) (102145766957/200000000000 : ℝ) (513767377793/1000000000000 : ℝ) (2568836889/5000000000 : ℝ) (25687919619/50000000000 : ℝ) (513758392387/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1073/8192 : ℝ))) 3 (513767377793/1000000000000 : ℝ) (2568836889/5000000000 : ℝ) (25687919619/50000000000 : ℝ) (513758392387/1000000000000 : ℝ) (256881442543/500000000000 : ℝ) (256881442547/500000000000 : ℝ) (256881442533/500000000000 : ℝ) (256881442537/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1073/8192 : ℝ))) 4 (256881442543/500000000000 : ℝ) (256881442547/500000000000 : ℝ) (256881442533/500000000000 : ℝ) (256881442537/500000000000 : ℝ) (128440721269/250000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1073/8192 : ℝ))) 5 (128440721269/250000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1073/8192 : ℝ))) 6 (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1073/8192 : ℝ))) 7 (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1073/8192 : ℝ)) hmem 8 (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1073/8192 : ℝ))) hcmem 8 (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1073/8192 : ℝ)) (990709491061/1000000000000 : ℝ) (123838686383/125000000000 : ℝ) (20550515403/40000000000 : ℝ) (128440721271/250000000000 : ℝ) (203646189927/250000000000 : ℝ) (407292379863/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0095_exp_lower
  have heNumeric : (252381983873/125000000000 : ℝ)/4 ≤ Real.exp (-2734657398279/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (252381983873/125000000000 : ℝ)/4 ≤ Real.exp ((2145/16384 : ℝ)-(407292379863/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2145/16384 : ℝ) (1073/8192 : ℝ) (407292379863/500000000000 : ℝ) (252381983873/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0096; no trusted numerical premise.
theorem cover7_leaf0096_exp_radius : (199532538295041563/200000000000000000 : ℝ) ≤ Real.exp ((-2147/114688 : ℝ)/8) ∧ Real.exp ((-2147/114688 : ℝ)/8) ≤ (124707836434400977/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2147/114688 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0096_exp_lower : (918091477022592259/1000000000000000000 : ℝ) ≤ Real.exp ((-273466384491/400000000000 : ℝ)/8) ∧ Real.exp ((-273466384491/400000000000 : ℝ)/8) ≤ (45904573851129613/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-273466384491/400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0096_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2019052616959/1000000000000 : ℝ) ≤ 4*Real.exp (1073/8192 : ℝ)*Real.exp (-mu (radius 7 (2147/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (2019052616959/1000000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2147/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0096_exp_radius
  have hrNumeric : (981453783149/1000000000000 : ℝ) ≤ Real.exp (-2147/114688 : ℝ) ∧ Real.exp (-2147/114688 : ℝ) ≤ (19629075663/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981453783149/1000000000000 : ℝ) ≤ (radius 7 (2147/16384 : ℝ)) ∧ (radius 7 (2147/16384 : ℝ)) ≤ (19629075663/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2147/16384 : ℝ)) (981453783149/1000000000000 : ℝ) (19629075663/20000000000 : ℝ) (191698908553/1000000000000 : ℝ) (191698908559/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2147/16384 : ℝ)) (981453783149/1000000000000 : ℝ) (19629075663/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2147/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981453783149/1000000000000 : ℝ) (19629075663/20000000000 : ℝ) (495363445787/500000000000 : ℝ) (39629075663/40000000000 : ℝ) (495341746461/500000000000 : ℝ) (990683492923/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2147/16384 : ℝ)) 1 (495363445787/500000000000 : ℝ) (39629075663/40000000000 : ℝ) (495341746461/500000000000 : ℝ) (990683492923/1000000000000 : ℝ) (123838149031/125000000000 : ℝ) (990705192249/1000000000000 : ℝ) (99070519201/100000000000 : ℝ) (247676298003/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2147/16384 : ℝ)) 2 (123838149031/125000000000 : ℝ) (990705192249/1000000000000 : ℝ) (99070519201/100000000000 : ℝ) (247676298003/250000000000 : ℝ) (990705192129/1000000000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2147/16384 : ℝ)) 3 (990705192129/1000000000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2147/16384 : ℝ)) 4 (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2147/16384 : ℝ)) 5 (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2147/16384 : ℝ)) 6 (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2147/16384 : ℝ)) 7 (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2147/16384 : ℝ))) (191698908553/1000000000000 : ℝ) (191698908559/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2147/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (191698908553/1000000000000 : ℝ) (191698908559/1000000000000 : ℝ) (148962363569/250000000000 : ℝ) (14896236357/25000000000 : ℝ) (218917169583/500000000000 : ℝ) (437834339173/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2147/16384 : ℝ))) 1 (148962363569/250000000000 : ℝ) (14896236357/25000000000 : ℝ) (218917169583/500000000000 : ℝ) (437834339173/1000000000000 : ℝ) (516841896721/1000000000000 : ℝ) (516841896727/1000000000000 : ℝ) (510767414833/1000000000000 : ℝ) (510767414839/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2147/16384 : ℝ))) 2 (516841896721/1000000000000 : ℝ) (516841896727/1000000000000 : ℝ) (510767414833/1000000000000 : ℝ) (510767414839/1000000000000 : ℝ) (513804655777/1000000000000 : ℝ) (513804655783/1000000000000 : ℝ) (256897839357/500000000000 : ℝ) (513795678721/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2147/16384 : ℝ))) 3 (513804655777/1000000000000 : ℝ) (513804655783/1000000000000 : ℝ) (256897839357/500000000000 : ℝ) (513795678721/1000000000000 : ℝ) (102760033449/200000000000 : ℝ) (128450041813/250000000000 : ℝ) (20552006689/40000000000 : ℝ) (513800167233/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2147/16384 : ℝ))) 4 (102760033449/200000000000 : ℝ) (128450041813/250000000000 : ℝ) (20552006689/40000000000 : ℝ) (513800167233/1000000000000 : ℝ) (102760033447/200000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2147/16384 : ℝ))) 5 (102760033447/200000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2147/16384 : ℝ))) 6 (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2147/16384 : ℝ))) 7 (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2147/16384 : ℝ)) hmem 8 (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2147/16384 : ℝ))) hcmem 8 (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2147/16384 : ℝ)) (15479768627/15625000000 : ℝ) (990705192131/1000000000000 : ℝ) (256900083617/500000000000 : ℝ) (513800167243/1000000000000 : ℝ) (407323703261/500000000000 : ℝ) (40732370327/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0096_exp_lower
  have heNumeric : (2019052616959/1000000000000 : ℝ)/4 ≤ Real.exp (-273466384491/400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2019052616959/1000000000000 : ℝ)/4 ≤ Real.exp ((1073/8192 : ℝ)-(40732370327/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (1073/8192 : ℝ) (2147/16384 : ℝ) (40732370327/50000000000 : ℝ) (2019052616959/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0097; no trusted numerical premise.
theorem cover7_leaf0097_exp_radius : (997661604109760043/1000000000000000000 : ℝ) ≤ Real.exp ((-537/28672 : ℝ)/8) ∧ Real.exp ((-537/28672 : ℝ)/8) ≤ (249415401027440011/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-537/28672 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0097_exp_lower : (28690352947149331/31250000000000000 : ℝ) ≤ Real.exp ((-546934042677/800000000000 : ℝ)/8) ∧ Real.exp ((-546934042677/800000000000 : ℝ)/8) ≤ (918091294308778593/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-546934042677/800000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0097_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (201904940239/100000000000 : ℝ) ≤ 4*Real.exp (2147/16384 : ℝ)*Real.exp (-mu (radius 7 (537/4096 : ℝ))) ∧ (2019/1000 : ℝ) < (201904940239/100000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (537/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0097_exp_radius
  have hrNumeric : (245361306397/250000000000 : ℝ) ≤ Real.exp (-537/28672 : ℝ) ∧ Real.exp (-537/28672 : ℝ) ≤ (981445225589/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245361306397/250000000000 : ℝ) ≤ (radius 7 (537/4096 : ℝ)) ∧ (radius 7 (537/4096 : ℝ)) ≤ (981445225589/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (537/4096 : ℝ)) (245361306397/250000000000 : ℝ) (981445225589/1000000000000 : ℝ) (47935679019/250000000000 : ℝ) (191742716083/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (537/4096 : ℝ)) (245361306397/250000000000 : ℝ) (981445225589/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (537/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245361306397/250000000000 : ℝ) (981445225589/1000000000000 : ℝ) (495361306397/500000000000 : ℝ) (198144522559/200000000000 : ℝ) (495339586947/500000000000 : ℝ) (198135834779/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (537/4096 : ℝ)) 1 (495361306397/500000000000 : ℝ) (198144522559/200000000000 : ℝ) (495339586947/500000000000 : ℝ) (198135834779/200000000000 : ℝ) (30959402917/31250000000 : ℝ) (198140178669/200000000000 : ℝ) (198140178621/200000000000 : ℝ) (990700893107/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (537/4096 : ℝ)) 2 (30959402917/31250000000 : ℝ) (198140178669/200000000000 : ℝ) (198140178621/200000000000 : ℝ) (990700893107/1000000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (537/4096 : ℝ)) 3 (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (537/4096 : ℝ)) 4 (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (537/4096 : ℝ)) 5 (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (537/4096 : ℝ)) 6 (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (537/4096 : ℝ)) 7 (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (537/4096 : ℝ))) (47935679019/250000000000 : ℝ) (191742716083/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (537/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (47935679019/250000000000 : ℝ) (191742716083/1000000000000 : ℝ) (297935679019/500000000000 : ℝ) (297935679021/500000000000 : ℝ) (437884363817/1000000000000 : ℝ) (218942181913/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (537/4096 : ℝ))) 1 (297935679019/500000000000 : ℝ) (297935679021/500000000000 : ℝ) (437884363817/1000000000000 : ℝ) (218942181913/500000000000 : ℝ) (516877860927/1000000000000 : ℝ) (258438930467/500000000000 : ℝ) (510805981299/1000000000000 : ℝ) (510805981307/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (537/4096 : ℝ))) 2 (516877860927/1000000000000 : ℝ) (258438930467/500000000000 : ℝ) (510805981299/1000000000000 : ℝ) (510805981307/1000000000000 : ℝ) (513841921113/1000000000000 : ℝ) (513841921121/1000000000000 : ℝ) (51383295239/100000000000 : ℝ) (513832952399/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (537/4096 : ℝ))) 3 (513841921113/1000000000000 : ℝ) (513841921121/1000000000000 : ℝ) (51383295239/100000000000 : ℝ) (513832952399/1000000000000 : ℝ) (513837436751/1000000000000 : ℝ) (12845935919/25000000000 : ℝ) (513837436731/1000000000000 : ℝ) (513837436741/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (537/4096 : ℝ))) 4 (513837436751/1000000000000 : ℝ) (12845935919/25000000000 : ℝ) (513837436731/1000000000000 : ℝ) (513837436741/1000000000000 : ℝ) (513837436741/1000000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (537/4096 : ℝ))) 5 (513837436741/1000000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (537/4096 : ℝ))) 6 (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (537/4096 : ℝ))) 7 (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (537/4096 : ℝ)) hmem 8 (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (537/4096 : ℝ))) hcmem 8 (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (537/4096 : ℝ)) (123837611653/125000000000 : ℝ) (495350446613/500000000000 : ℝ) (25691871837/50000000000 : ℝ) (513837436751/1000000000000 : ℝ) (162942006759/200000000000 : ℝ) (162942006763/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0097_exp_lower
  have heNumeric : (201904940239/100000000000 : ℝ)/4 ≤ Real.exp (-546934042677/800000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (201904940239/100000000000 : ℝ)/4 ≤ Real.exp ((2147/16384 : ℝ)-(162942006763/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2147/16384 : ℝ) (537/4096 : ℝ) (162942006763/200000000000 : ℝ) (201904940239/100000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0098; no trusted numerical premise.
theorem cover7_leaf0098_exp_radius : (199532103349099481/200000000000000000 : ℝ) ≤ Real.exp ((-307/16384 : ℝ)/8) ∧ Real.exp ((-307/16384 : ℝ)/8) ≤ (498830258372748703/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-307/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0098_exp_lower : (45904555691826037/50000000000000000 : ℝ) ≤ Real.exp ((-683669125933/1000000000000 : ℝ)/8) ∧ Real.exp ((-683669125933/1000000000000 : ℝ)/8) ≤ (918091113836520741/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-683669125933/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0098_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1009523113631/500000000000 : ℝ) ≤ 4*Real.exp (537/4096 : ℝ)*Real.exp (-mu (radius 7 (2149/16384 : ℝ))) ∧ (2019/1000 : ℝ) < (1009523113631/500000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (2149/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0098_exp_radius
  have hrNumeric : (490718334051/500000000000 : ℝ) ≤ Real.exp (-307/16384 : ℝ) ∧ Real.exp (-307/16384 : ℝ) ≤ (981436668103/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (490718334051/500000000000 : ℝ) ≤ (radius 7 (2149/16384 : ℝ)) ∧ (radius 7 (2149/16384 : ℝ)) ≤ (981436668103/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (2149/16384 : ℝ)) (490718334051/500000000000 : ℝ) (981436668103/1000000000000 : ℝ) (47946628207/250000000000 : ℝ) (95893256417/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (2149/16384 : ℝ)) (490718334051/500000000000 : ℝ) (981436668103/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (2149/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (490718334051/500000000000 : ℝ) (981436668103/1000000000000 : ℝ) (990718334051/1000000000000 : ℝ) (247679583513/250000000000 : ℝ) (198134970977/200000000000 : ℝ) (495337427443/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (2149/16384 : ℝ)) 1 (990718334051/1000000000000 : ℝ) (247679583513/250000000000 : ℝ) (198134970977/200000000000 : ℝ) (495337427443/500000000000 : ℝ) (247674148617/250000000000 : ℝ) (990696594469/1000000000000 : ℝ) (990696594229/1000000000000 : ℝ) (990696594231/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (2149/16384 : ℝ)) 2 (247674148617/250000000000 : ℝ) (990696594469/1000000000000 : ℝ) (990696594229/1000000000000 : ℝ) (990696594231/1000000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (2149/16384 : ℝ)) 3 (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (2149/16384 : ℝ)) 4 (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (2149/16384 : ℝ)) 5 (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (2149/16384 : ℝ)) 6 (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (2149/16384 : ℝ)) 7 (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (2149/16384 : ℝ))) (47946628207/250000000000 : ℝ) (95893256417/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (2149/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (47946628207/250000000000 : ℝ) (95893256417/500000000000 : ℝ) (297946628207/500000000000 : ℝ) (595893256417/1000000000000 : ℝ) (437934370457/1000000000000 : ℝ) (87586874093/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (2149/16384 : ℝ))) 1 (297946628207/500000000000 : ℝ) (595893256417/1000000000000 : ℝ) (437934370457/1000000000000 : ℝ) (87586874093/200000000000 : ℝ) (103382762687/200000000000 : ℝ) (516913813441/1000000000000 : ℝ) (102168906837/200000000000 : ℝ) (31927783387/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (2149/16384 : ℝ))) 2 (103382762687/200000000000 : ℝ) (516913813441/1000000000000 : ℝ) (102168906837/200000000000 : ℝ) (31927783387/62500000000 : ℝ) (51387917381/100000000000 : ℝ) (513879173817/1000000000000 : ℝ) (513870213417/1000000000000 : ℝ) (20554808537/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (2149/16384 : ℝ))) 3 (51387917381/100000000000 : ℝ) (513879173817/1000000000000 : ℝ) (513870213417/1000000000000 : ℝ) (20554808537/40000000000 : ℝ) (513874693613/1000000000000 : ℝ) (513874693621/1000000000000 : ℝ) (513874693593/1000000000000 : ℝ) (256937346801/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (2149/16384 : ℝ))) 4 (513874693613/1000000000000 : ℝ) (513874693621/1000000000000 : ℝ) (513874693593/1000000000000 : ℝ) (256937346801/500000000000 : ℝ) (513874693603/1000000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (2149/16384 : ℝ))) 5 (513874693603/1000000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (2149/16384 : ℝ))) 6 (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (2149/16384 : ℝ))) 7 (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (2149/16384 : ℝ)) hmem 8 (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (2149/16384 : ℝ))) hcmem 8 (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (2149/16384 : ℝ)) (247674148587/250000000000 : ℝ) (19813931887/20000000000 : ℝ) (256937346801/500000000000 : ℝ) (128468673403/250000000000 : ℝ) (814772641539/1000000000000 : ℝ) (407386320779/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0098_exp_lower
  have heNumeric : (1009523113631/500000000000 : ℝ)/4 ≤ Real.exp (-683669125933/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1009523113631/500000000000 : ℝ)/4 ≤ Real.exp ((537/4096 : ℝ)-(407386320779/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (537/4096 : ℝ) (2149/16384 : ℝ) (407386320779/500000000000 : ℝ) (1009523113631/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover7_leaf0099; no trusted numerical premise.
theorem cover7_leaf0099_exp_radius : (997659429382419899/1000000000000000000 : ℝ) ≤ Real.exp ((-1075/57344 : ℝ)/8) ∧ Real.exp ((-1075/57344 : ℝ)/8) ≤ (9976594293824199/10000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1075/57344 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0099_exp_lower : (459045467801761077/500000000000000000 : ℝ) ≤ Real.exp ((-2734682716031/4000000000000 : ℝ)/8) ∧ Real.exp ((-2734682716031/4000000000000 : ℝ)/8) ≤ (183618187120704431/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2734682716031/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover7_leaf0099_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (403808618307/200000000000 : ℝ) ≤ 4*Real.exp (2149/16384 : ℝ)*Real.exp (-mu (radius 7 (1075/8192 : ℝ))) ∧ (2019/1000 : ℝ) < (403808618307/200000000000 : ℝ) := by
  have hmem := radius_mem 7 (by norm_num) (1075/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0099_exp_radius
  have hrNumeric : (981428110691/1000000000000 : ℝ) ≤ Real.exp (-1075/57344 : ℝ) ∧ Real.exp (-1075/57344 : ℝ) ≤ (245357027673/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (981428110691/1000000000000 : ℝ) ≤ (radius 7 (1075/8192 : ℝ)) ∧ (radius 7 (1075/8192 : ℝ)) ≤ (245357027673/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 7 (1075/8192 : ℝ)) (981428110691/1000000000000 : ℝ) (245357027673/250000000000 : ℝ) (38366059763/200000000000 : ℝ) (191830298821/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 7 (1075/8192 : ℝ)) (981428110691/1000000000000 : ℝ) (245357027673/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 7 (1075/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (981428110691/1000000000000 : ℝ) (245357027673/250000000000 : ℝ) (198142811069/200000000000 : ℝ) (495357027673/500000000000 : ℝ) (198134107179/200000000000 : ℝ) (123833816987/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 7 (1075/8192 : ℝ)) 1 (198142811069/200000000000 : ℝ) (495357027673/500000000000 : ℝ) (198134107179/200000000000 : ℝ) (123833816987/125000000000 : ℝ) (49534614781/50000000000 : ℝ) (990692295621/1000000000000 : ℝ) (990692295381/1000000000000 : ℝ) (990692295383/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 7 (1075/8192 : ℝ)) 2 (49534614781/50000000000 : ℝ) (990692295621/1000000000000 : ℝ) (990692295381/1000000000000 : ℝ) (990692295383/1000000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 7 (1075/8192 : ℝ)) 3 (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 7 (1075/8192 : ℝ)) 4 (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 7 (1075/8192 : ℝ)) 5 (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 7 (1075/8192 : ℝ)) 6 (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 7 (1075/8192 : ℝ)) 7 (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 7 (1075/8192 : ℝ))) (38366059763/200000000000 : ℝ) (191830298821/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 7 (1075/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (38366059763/200000000000 : ℝ) (191830298821/1000000000000 : ℝ) (595915149407/1000000000000 : ℝ) (595915149411/1000000000000 : ℝ) (218992179549/500000000000 : ℝ) (218992179553/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 7 (1075/8192 : ℝ))) 1 (595915149407/1000000000000 : ℝ) (595915149411/1000000000000 : ℝ) (218992179549/500000000000 : ℝ) (218992179553/500000000000 : ℝ) (129237438563/250000000000 : ℝ) (516949754259/1000000000000 : ℝ) (1021766147/2000000000 : ℝ) (127720768377/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 7 (1075/8192 : ℝ))) 2 (129237438563/250000000000 : ℝ) (516949754259/1000000000000 : ℝ) (1021766147/2000000000 : ℝ) (127720768377/250000000000 : ℝ) (128479103469/250000000000 : ℝ) (128479103471/250000000000 : ℝ) (513907461803/1000000000000 : ℝ) (128476865453/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 7 (1075/8192 : ℝ))) 3 (128479103469/250000000000 : ℝ) (128479103471/250000000000 : ℝ) (513907461803/1000000000000 : ℝ) (128476865453/250000000000 : ℝ) (513911937839/1000000000000 : ℝ) (64238992231/125000000000 : ℝ) (25695596891/50000000000 : ℝ) (513911937829/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 7 (1075/8192 : ℝ))) 4 (513911937839/1000000000000 : ℝ) (64238992231/125000000000 : ℝ) (25695596891/50000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 7 (1075/8192 : ℝ))) 5 (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 7 (1075/8192 : ℝ))) 6 (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 7 (1075/8192 : ℝ))) 7 (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 7 (1075/8192 : ℝ)) hmem 8 (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 7 (1075/8192 : ℝ))) hcmem 8 (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 7 (1075/8192 : ℝ)) (1981384591/2000000000 : ℝ) (495346147751/500000000000 : ℝ) (513911937829/1000000000000 : ℝ) (513911937839/1000000000000 : ℝ) (814835229771/1000000000000 : ℝ) (814835229789/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover7_leaf0099_exp_lower
  have heNumeric : (403808618307/200000000000 : ℝ)/4 ≤ Real.exp (-2734682716031/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (403808618307/200000000000 : ℝ)/4 ≤ Real.exp ((2149/16384 : ℝ)-(814835229789/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 7 (2149/16384 : ℝ) (1075/8192 : ℝ) (814835229789/1000000000000 : ℝ) (403808618307/200000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover7_leaf0075_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0075_certificate
#check SmaleRate.Proofs.cover7_leaf0076_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0076_certificate
#check SmaleRate.Proofs.cover7_leaf0077_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0077_certificate
#check SmaleRate.Proofs.cover7_leaf0078_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0078_certificate
#check SmaleRate.Proofs.cover7_leaf0079_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0079_certificate
#check SmaleRate.Proofs.cover7_leaf0080_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0080_certificate
#check SmaleRate.Proofs.cover7_leaf0081_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0081_certificate
#check SmaleRate.Proofs.cover7_leaf0082_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0082_certificate
#check SmaleRate.Proofs.cover7_leaf0083_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0083_certificate
#check SmaleRate.Proofs.cover7_leaf0084_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0084_certificate
#check SmaleRate.Proofs.cover7_leaf0085_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0085_certificate
#check SmaleRate.Proofs.cover7_leaf0086_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0086_certificate
#check SmaleRate.Proofs.cover7_leaf0087_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0087_certificate
#check SmaleRate.Proofs.cover7_leaf0088_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0088_certificate
#check SmaleRate.Proofs.cover7_leaf0089_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0089_certificate
#check SmaleRate.Proofs.cover7_leaf0090_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0090_certificate
#check SmaleRate.Proofs.cover7_leaf0091_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0091_certificate
#check SmaleRate.Proofs.cover7_leaf0092_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0092_certificate
#check SmaleRate.Proofs.cover7_leaf0093_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0093_certificate
#check SmaleRate.Proofs.cover7_leaf0094_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0094_certificate
#check SmaleRate.Proofs.cover7_leaf0095_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0095_certificate
#check SmaleRate.Proofs.cover7_leaf0096_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0096_certificate
#check SmaleRate.Proofs.cover7_leaf0097_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0097_certificate
#check SmaleRate.Proofs.cover7_leaf0098_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0098_certificate
#check SmaleRate.Proofs.cover7_leaf0099_certificate
#print axioms SmaleRate.Proofs.cover7_leaf0099_certificate
