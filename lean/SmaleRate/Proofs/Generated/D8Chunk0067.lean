/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1675; no trusted numerical premise.
theorem cover8_leaf1675_exp_radius : (997854630042321249/1000000000000000000 : ℝ) ≤ Real.exp ((-563/32768 : ℝ)/8) ∧ Real.exp ((-563/32768 : ℝ)/8) ≤ (798283704033857/800000000000000 : ℝ) := by
  have h := exp_small_bounds ((-563/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1675_exp_lower : (460056803632835983/500000000000000000 : ℝ) ≤ Real.exp ((-166516260809/250000000000 : ℝ)/8) ∧ Real.exp ((-166516260809/250000000000 : ℝ)/8) ≤ (920113607265671967/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166516260809/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1675_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027452191471/500000000000 : ℝ) ≤ 4*Real.exp (281/2048 : ℝ)*Real.exp (-mu (radius 8 (563/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027452191471/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (563/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1675_exp_radius
  have hrNumeric : (491482681/500000000 : ℝ) ≤ Real.exp (-563/32768 : ℝ) ∧ Real.exp (-563/32768 : ℝ) ≤ (982965362001/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491482681/500000000 : ℝ) ≤ (radius 8 (563/4096 : ℝ)) ∧ (radius 8 (563/4096 : ℝ)) ≤ (982965362001/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (563/4096 : ℝ)) (491482681/500000000 : ℝ) (982965362001/1000000000000 : ℝ) (183790905939/1000000000000 : ℝ) (91895452973/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (563/4096 : ℝ)) (491482681/500000000 : ℝ) (982965362001/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (563/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491482681/500000000 : ℝ) (982965362001/1000000000000 : ℝ) (991482681/1000000000 : ℝ) (991482681001/1000000000000 : ℝ) (495723048183/500000000000 : ℝ) (991446096367/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (563/4096 : ℝ)) 1 (991482681/1000000000 : ℝ) (991482681001/1000000000000 : ℝ) (495723048183/500000000000 : ℝ) (991446096367/1000000000000 : ℝ) (991464388683/1000000000000 : ℝ) (247866097171/250000000000 : ℝ) (495732194257/500000000000 : ℝ) (247866097129/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (563/4096 : ℝ)) 2 (991464388683/1000000000000 : ℝ) (247866097171/250000000000 : ℝ) (495732194257/500000000000 : ℝ) (247866097129/250000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (563/4096 : ℝ)) 3 (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (563/4096 : ℝ)) 4 (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (563/4096 : ℝ)) 5 (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (563/4096 : ℝ)) 6 (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (563/4096 : ℝ)) 7 (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (563/4096 : ℝ))) (183790905939/1000000000000 : ℝ) (91895452973/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (563/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (183790905939/1000000000000 : ℝ) (91895452973/500000000000 : ℝ) (591895452969/1000000000000 : ℝ) (591895452973/1000000000000 : ℝ) (107177103997/250000000000 : ℝ) (428708415997/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (563/4096 : ℝ))) 1 (591895452969/1000000000000 : ℝ) (591895452973/1000000000000 : ℝ) (107177103997/250000000000 : ℝ) (428708415997/1000000000000 : ℝ) (255150967239/500000000000 : ℝ) (102060386897/200000000000 : ℝ) (251868299947/500000000000 : ℝ) (251868299951/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (563/4096 : ℝ))) 2 (255150967239/500000000000 : ℝ) (102060386897/200000000000 : ℝ) (251868299947/500000000000 : ℝ) (251868299951/500000000000 : ℝ) (253509633593/500000000000 : ℝ) (253509633597/500000000000 : ℝ) (507008640353/1000000000000 : ℝ) (253504320181/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (563/4096 : ℝ))) 3 (253509633593/500000000000 : ℝ) (253509633597/500000000000 : ℝ) (507008640353/1000000000000 : ℝ) (253504320181/500000000000 : ℝ) (507013953769/1000000000000 : ℝ) (253506976889/500000000000 : ℝ) (507013953741/1000000000000 : ℝ) (507013953751/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (563/4096 : ℝ))) 4 (507013953769/1000000000000 : ℝ) (253506976889/500000000000 : ℝ) (507013953741/1000000000000 : ℝ) (507013953751/1000000000000 : ℝ) (101402790751/200000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (563/4096 : ℝ))) 5 (101402790751/200000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (563/4096 : ℝ))) 6 (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (563/4096 : ℝ))) 7 (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (563/4096 : ℝ)) hmem 8 (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (563/4096 : ℝ))) hcmem 8 (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (563/4096 : ℝ)) (495732194299/500000000000 : ℝ) (4957321943/5000000000 : ℝ) (253506976877/500000000000 : ℝ) (101402790753/200000000000 : ℝ) (401636037233/500000000000 : ℝ) (401636037243/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1675_exp_lower
  have heNumeric : (1027452191471/500000000000 : ℝ)/4 ≤ Real.exp (-166516260809/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027452191471/500000000000 : ℝ)/4 ≤ Real.exp ((281/2048 : ℝ)-(401636037243/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (281/2048 : ℝ) (563/4096 : ℝ) (401636037243/500000000000 : ℝ) (1027452191471/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1676; no trusted numerical premise.
theorem cover8_leaf1676_exp_radius : (498925411768126437/500000000000000000 : ℝ) ≤ Real.exp ((-141/8192 : ℝ)/8) ∧ Real.exp ((-141/8192 : ℝ)/8) ≤ (7982806588290023/8000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-141/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1676_exp_lower : (18402299833889801/20000000000000000 : ℝ) ≤ Real.exp ((-33302650311/50000000000 : ℝ)/8) ∧ Real.exp ((-33302650311/50000000000 : ℝ)/8) ≤ (920114991694490051/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33302650311/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1676_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256866139751/125000000000 : ℝ) ≤ 4*Real.exp (563/4096 : ℝ)*Real.exp (-mu (radius 8 (141/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (256866139751/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (141/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1676_exp_radius
  have hrNumeric : (7679182537/7812500000 : ℝ) ≤ Real.exp (-141/8192 : ℝ) ∧ Real.exp (-141/8192 : ℝ) ≤ (982935364737/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (7679182537/7812500000 : ℝ) ≤ (radius 8 (141/1024 : ℝ)) ∧ (radius 8 (141/1024 : ℝ)) ≤ (982935364737/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (141/1024 : ℝ)) (7679182537/7812500000 : ℝ) (982935364737/1000000000000 : ℝ) (183951267321/1000000000000 : ℝ) (359279819/1953125000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (141/1024 : ℝ)) (7679182537/7812500000 : ℝ) (982935364737/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (141/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (7679182537/7812500000 : ℝ) (982935364737/1000000000000 : ℝ) (15491682537/15625000000 : ℝ) (991467682369/1000000000000 : ℝ) (198286193643/200000000000 : ℝ) (123928871027/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (141/1024 : ℝ)) 1 (15491682537/15625000000 : ℝ) (991467682369/1000000000000 : ℝ) (198286193643/200000000000 : ℝ) (123928871027/125000000000 : ℝ) (991449325291/1000000000000 : ℝ) (991449325293/1000000000000 : ℝ) (991449325121/1000000000000 : ℝ) (991449325123/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (141/1024 : ℝ)) 2 (991449325291/1000000000000 : ℝ) (991449325293/1000000000000 : ℝ) (991449325121/1000000000000 : ℝ) (991449325123/1000000000000 : ℝ) (495724662603/500000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (141/1024 : ℝ)) 3 (495724662603/500000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (141/1024 : ℝ)) 4 (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (141/1024 : ℝ)) 5 (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (141/1024 : ℝ)) 6 (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (141/1024 : ℝ)) 7 (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (141/1024 : ℝ))) (183951267321/1000000000000 : ℝ) (359279819/1953125000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (141/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (183951267321/1000000000000 : ℝ) (359279819/1953125000 : ℝ) (29598781683/50000000000 : ℝ) (2312404819/3906250000 : ℝ) (428895403707/1000000000000 : ℝ) (107223850929/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (141/1024 : ℝ))) 1 (29598781683/50000000000 : ℝ) (2312404819/3906250000 : ℝ) (428895403707/1000000000000 : ℝ) (107223850929/250000000000 : ℝ) (510435518683/1000000000000 : ℝ) (51043551869/100000000000 : ℝ) (503880569563/1000000000000 : ℝ) (503880569571/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (141/1024 : ℝ))) 2 (510435518683/1000000000000 : ℝ) (51043551869/100000000000 : ℝ) (503880569563/1000000000000 : ℝ) (503880569571/1000000000000 : ℝ) (507158044123/1000000000000 : ℝ) (507158044131/1000000000000 : ℝ) (507147453783/1000000000000 : ℝ) (15848357931/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (141/1024 : ℝ))) 3 (507158044123/1000000000000 : ℝ) (507158044131/1000000000000 : ℝ) (507147453783/1000000000000 : ℝ) (15848357931/31250000000 : ℝ) (507152748953/1000000000000 : ℝ) (253576374481/500000000000 : ℝ) (20286109957/40000000000 : ℝ) (253576374467/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (141/1024 : ℝ))) 4 (507152748953/1000000000000 : ℝ) (253576374481/500000000000 : ℝ) (20286109957/40000000000 : ℝ) (253576374467/500000000000 : ℝ) (507152748939/1000000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (141/1024 : ℝ))) 5 (507152748939/1000000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (141/1024 : ℝ))) 6 (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (141/1024 : ℝ))) 7 (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (141/1024 : ℝ)) hmem 8 (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (141/1024 : ℝ))) hcmem 8 (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (141/1024 : ℝ)) (198289865041/200000000000 : ℝ) (123931165651/125000000000 : ℝ) (253576374469/500000000000 : ℝ) (126788187237/250000000000 : ℝ) (200876044519/250000000000 : ℝ) (160700835619/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1676_exp_lower
  have heNumeric : (256866139751/125000000000 : ℝ)/4 ≤ Real.exp (-33302650311/50000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256866139751/125000000000 : ℝ)/4 ≤ Real.exp ((563/4096 : ℝ)-(160700835619/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (563/4096 : ℝ) (141/1024 : ℝ) (160700835619/200000000000 : ℝ) (256866139751/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1677; no trusted numerical premise.
theorem cover8_leaf1677_exp_radius : (997847017044705139/1000000000000000000 : ℝ) ≤ Real.exp ((-565/32768 : ℝ)/8) ∧ Real.exp ((-565/32768 : ℝ)/8) ≤ (49892350852235257/50000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-565/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1677_exp_lower : (920116408025941511/1000000000000000000 : ℝ) ≤ Real.exp ((-666040691843/1000000000000 : ℝ)/8) ∧ Real.exp ((-666040691843/1000000000000 : ℝ)/8) ≤ (115014551003242689/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666040691843/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1677_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410990884667/200000000000 : ℝ) ≤ 4*Real.exp (141/1024 : ℝ)*Real.exp (-mu (radius 8 (565/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (410990884667/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (565/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1677_exp_radius
  have hrNumeric : (982905368387/1000000000000 : ℝ) ≤ Real.exp (-565/32768 : ℝ) ∧ Real.exp (-565/32768 : ℝ) ≤ (245726342097/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982905368387/1000000000000 : ℝ) ≤ (radius 8 (565/4096 : ℝ)) ∧ (radius 8 (565/4096 : ℝ)) ≤ (245726342097/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (565/4096 : ℝ)) (982905368387/1000000000000 : ℝ) (245726342097/250000000000 : ℝ) (23013934907/125000000000 : ℝ) (92055739631/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (565/4096 : ℝ)) (982905368387/1000000000000 : ℝ) (245726342097/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (565/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982905368387/1000000000000 : ℝ) (245726342097/250000000000 : ℝ) (991452684193/1000000000000 : ℝ) (495726342097/500000000000 : ℝ) (495707920147/500000000000 : ℝ) (123926980037/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (565/4096 : ℝ)) 1 (991452684193/1000000000000 : ℝ) (495726342097/500000000000 : ℝ) (495707920147/500000000000 : ℝ) (123926980037/125000000000 : ℝ) (991434262243/1000000000000 : ℝ) (198286852449/200000000000 : ℝ) (123929282759/125000000000 : ℝ) (495717131037/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (565/4096 : ℝ)) 2 (991434262243/1000000000000 : ℝ) (198286852449/200000000000 : ℝ) (123929282759/125000000000 : ℝ) (495717131037/500000000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (565/4096 : ℝ)) 3 (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (565/4096 : ℝ)) 4 (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (565/4096 : ℝ)) 5 (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (565/4096 : ℝ)) 6 (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (565/4096 : ℝ)) 7 (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (565/4096 : ℝ))) (23013934907/125000000000 : ℝ) (92055739631/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (565/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (23013934907/125000000000 : ℝ) (92055739631/500000000000 : ℝ) (148013934907/250000000000 : ℝ) (592055739631/1000000000000 : ℝ) (26817633487/62500000000 : ℝ) (2145410679/5000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (565/4096 : ℝ))) 1 (148013934907/250000000000 : ℝ) (592055739631/1000000000000 : ℝ) (26817633487/62500000000 : ℝ) (2145410679/5000000000 : ℝ) (51056893771/100000000000 : ℝ) (127642234429/250000000000 : ℝ) (504024345907/1000000000000 : ℝ) (252012172957/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (565/4096 : ℝ))) 2 (51056893771/100000000000 : ℝ) (127642234429/250000000000 : ℝ) (504024345907/1000000000000 : ℝ) (252012172957/500000000000 : ℝ) (31706040113/62500000000 : ℝ) (101459328363/200000000000 : ℝ) (253643043897/500000000000 : ℝ) (507286087801/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (565/4096 : ℝ))) 3 (31706040113/62500000000 : ℝ) (101459328363/200000000000 : ℝ) (253643043897/500000000000 : ℝ) (507286087801/1000000000000 : ℝ) (507291364801/1000000000000 : ℝ) (63411420601/125000000000 : ℝ) (507291364773/1000000000000 : ℝ) (507291364781/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (565/4096 : ℝ))) 4 (507291364801/1000000000000 : ℝ) (63411420601/125000000000 : ℝ) (507291364773/1000000000000 : ℝ) (507291364781/1000000000000 : ℝ) (507291364787/1000000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (565/4096 : ℝ))) 5 (507291364787/1000000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (565/4096 : ℝ))) 6 (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (565/4096 : ℝ))) 7 (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (565/4096 : ℝ)) hmem 8 (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (565/4096 : ℝ))) hcmem 8 (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (565/4096 : ℝ)) (991434262157/1000000000000 : ℝ) (12392928277/12500000000 : ℝ) (253645682393/500000000000 : ℝ) (101458272959/200000000000 : ℝ) (401868002163/500000000000 : ℝ) (803736004343/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1677_exp_lower
  have heNumeric : (410990884667/200000000000 : ℝ)/4 ≤ Real.exp (-666040691843/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410990884667/200000000000 : ℝ)/4 ≤ Real.exp ((141/1024 : ℝ)-(803736004343/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (141/1024 : ℝ) (565/4096 : ℝ) (803736004343/1000000000000 : ℝ) (410990884667/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1678; no trusted numerical premise.
theorem cover8_leaf1678_exp_radius : (99784321056767799/100000000000000000 : ℝ) ≤ Real.exp ((-283/16384 : ℝ)/8) ∧ Real.exp ((-283/16384 : ℝ)/8) ≤ (997843210567677991/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-283/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1678_exp_lower : (36804714246427437/40000000000000000 : ℝ) ≤ Real.exp ((-66602810097/100000000000 : ℝ)/8) ∧ Real.exp ((-66602810097/100000000000 : ℝ)/8) ≤ (460058928080342963/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-66602810097/100000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1678_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128436268573/62500000000 : ℝ) ≤ 4*Real.exp (565/4096 : ℝ)*Real.exp (-mu (radius 8 (283/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (128436268573/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (283/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1678_exp_radius
  have hrNumeric : (982875372953/1000000000000 : ℝ) ≤ Real.exp (-283/16384 : ℝ) ∧ Real.exp (-283/16384 : ℝ) ≤ (491437686477/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982875372953/1000000000000 : ℝ) ≤ (radius 8 (283/2048 : ℝ)) ∧ (radius 8 (283/2048 : ℝ)) ≤ (491437686477/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (283/2048 : ℝ)) (982875372953/1000000000000 : ℝ) (491437686477/500000000000 : ℝ) (92135771067/500000000000 : ℝ) (9213577107/50000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (283/2048 : ℝ)) (982875372953/1000000000000 : ℝ) (491437686477/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (283/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982875372953/1000000000000 : ℝ) (491437686477/500000000000 : ℝ) (247859421619/250000000000 : ℝ) (991437686477/1000000000000 : ℝ) (247850178151/250000000000 : ℝ) (495700356303/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (283/2048 : ℝ)) 1 (247859421619/250000000000 : ℝ) (991437686477/1000000000000 : ℝ) (247850178151/250000000000 : ℝ) (495700356303/500000000000 : ℝ) (49570959977/50000000000 : ℝ) (495709599771/500000000000 : ℝ) (991419199367/1000000000000 : ℝ) (99141919937/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (283/2048 : ℝ)) 2 (49570959977/50000000000 : ℝ) (495709599771/500000000000 : ℝ) (991419199367/1000000000000 : ℝ) (99141919937/100000000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (283/2048 : ℝ)) 3 (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (283/2048 : ℝ)) 4 (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (283/2048 : ℝ)) 5 (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (283/2048 : ℝ)) 6 (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (283/2048 : ℝ)) 7 (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (283/2048 : ℝ))) (92135771067/500000000000 : ℝ) (9213577107/50000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (283/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (92135771067/500000000000 : ℝ) (9213577107/50000000000 : ℝ) (592135771067/1000000000000 : ℝ) (59213577107/100000000000 : ℝ) (429268613031/1000000000000 : ℝ) (429268613039/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (283/2048 : ℝ))) 1 (592135771067/1000000000000 : ℝ) (59213577107/100000000000 : ℝ) (429268613031/1000000000000 : ℝ) (429268613039/1000000000000 : ℝ) (510702192049/1000000000000 : ℝ) (102140438411/200000000000 : ℝ) (100833585907/200000000000 : ℝ) (252083964771/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (283/2048 : ℝ))) 2 (510702192049/1000000000000 : ℝ) (102140438411/200000000000 : ℝ) (100833585907/200000000000 : ℝ) (252083964771/500000000000 : ℝ) (63429382599/125000000000 : ℝ) (507435060799/1000000000000 : ℝ) (63428067867/125000000000 : ℝ) (15857016967/31250000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (283/2048 : ℝ))) 3 (63429382599/125000000000 : ℝ) (507435060799/1000000000000 : ℝ) (63428067867/125000000000 : ℝ) (15857016967/31250000000 : ℝ) (63428725233/125000000000 : ℝ) (31714362617/62500000000 : ℝ) (126857450459/250000000000 : ℝ) (101485960369/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (283/2048 : ℝ))) 4 (63428725233/125000000000 : ℝ) (31714362617/62500000000 : ℝ) (126857450459/250000000000 : ℝ) (101485960369/200000000000 : ℝ) (10148596037/20000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (283/2048 : ℝ))) 5 (10148596037/20000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (283/2048 : ℝ))) 6 (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (283/2048 : ℝ))) 7 (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (283/2048 : ℝ)) hmem 8 (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (283/2048 : ℝ))) hcmem 8 (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (283/2048 : ℝ)) (991419199453/1000000000000 : ℝ) (30981849983/31250000000 : ℝ) (507429801849/1000000000000 : ℝ) (507429801859/1000000000000 : ℝ) (200991888519/250000000000 : ℝ) (160793510819/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1678_exp_lower
  have heNumeric : (128436268573/62500000000 : ℝ)/4 ≤ Real.exp (-66602810097/100000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128436268573/62500000000 : ℝ)/4 ≤ Real.exp ((565/4096 : ℝ)-(160793510819/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (565/4096 : ℝ) (283/2048 : ℝ) (160793510819/200000000000 : ℝ) (128436268573/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1679; no trusted numerical premise.
theorem cover8_leaf1679_exp_radius : (997839404105171371/1000000000000000000 : ℝ) ≤ Real.exp ((-567/32768 : ℝ)/8) ∧ Real.exp ((-567/32768 : ℝ)/8) ≤ (249459851026292843/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-567/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1679_exp_lower : (184023867200452183/200000000000000000 : ℝ) ≤ Real.exp ((-666015234441/1000000000000 : ℝ)/8) ∧ Real.exp ((-666015234441/1000000000000 : ℝ)/8) ≤ (230029834000565229/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-666015234441/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1679_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027503368901/500000000000 : ℝ) ≤ 4*Real.exp (283/2048 : ℝ)*Real.exp (-mu (radius 8 (567/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027503368901/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (567/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1679_exp_radius
  have hrNumeric : (196569075687/200000000000 : ℝ) ≤ Real.exp (-567/32768 : ℝ) ∧ Real.exp (-567/32768 : ℝ) ≤ (245711344609/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196569075687/200000000000 : ℝ) ≤ (radius 8 (567/4096 : ℝ)) ∧ (radius 8 (567/4096 : ℝ)) ≤ (245711344609/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (567/4096 : ℝ)) (196569075687/200000000000 : ℝ) (245711344609/250000000000 : ℝ) (92215728169/500000000000 : ℝ) (23053932043/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (567/4096 : ℝ)) (196569075687/200000000000 : ℝ) (245711344609/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (567/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196569075687/200000000000 : ℝ) (245711344609/250000000000 : ℝ) (991422689217/1000000000000 : ℝ) (495711344609/500000000000 : ℝ) (198277117029/200000000000 : ℝ) (991385585147/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (567/4096 : ℝ)) 1 (991422689217/1000000000000 : ℝ) (495711344609/500000000000 : ℝ) (198277117029/200000000000 : ℝ) (991385585147/1000000000000 : ℝ) (991404137181/1000000000000 : ℝ) (991404137183/1000000000000 : ℝ) (991404137007/1000000000000 : ℝ) (991404137009/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (567/4096 : ℝ)) 2 (991404137181/1000000000000 : ℝ) (991404137183/1000000000000 : ℝ) (991404137007/1000000000000 : ℝ) (991404137009/1000000000000 : ℝ) (495702068547/500000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (567/4096 : ℝ)) 3 (495702068547/500000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (567/4096 : ℝ)) 4 (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (567/4096 : ℝ)) 5 (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (567/4096 : ℝ)) 6 (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (567/4096 : ℝ)) 7 (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (567/4096 : ℝ))) (92215728169/500000000000 : ℝ) (23053932043/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (567/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (92215728169/500000000000 : ℝ) (23053932043/125000000000 : ℝ) (592215728169/1000000000000 : ℝ) (148053932043/250000000000 : ℝ) (214727418101/500000000000 : ℝ) (42945483621/100000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (567/4096 : ℝ))) 1 (592215728169/1000000000000 : ℝ) (148053932043/250000000000 : ℝ) (214727418101/500000000000 : ℝ) (42945483621/100000000000 : ℝ) (102167056437/200000000000 : ℝ) (510835282191/1000000000000 : ℝ) (504311321047/1000000000000 : ℝ) (252155660527/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (567/4096 : ℝ))) 2 (102167056437/200000000000 : ℝ) (510835282191/1000000000000 : ℝ) (504311321047/1000000000000 : ℝ) (252155660527/500000000000 : ℝ) (31723331351/62500000000 : ℝ) (507573301623/1000000000000 : ℝ) (507562819753/1000000000000 : ℝ) (507562819761/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (567/4096 : ℝ))) 3 (31723331351/62500000000 : ℝ) (507573301623/1000000000000 : ℝ) (507562819753/1000000000000 : ℝ) (507562819761/1000000000000 : ℝ) (126892015171/250000000000 : ℝ) (126892015173/250000000000 : ℝ) (507568060657/1000000000000 : ℝ) (101513612133/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (567/4096 : ℝ))) 4 (126892015171/250000000000 : ℝ) (126892015173/250000000000 : ℝ) (507568060657/1000000000000 : ℝ) (101513612133/200000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (567/4096 : ℝ))) 5 (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (567/4096 : ℝ))) 6 (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (567/4096 : ℝ))) 7 (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (567/4096 : ℝ)) hmem 8 (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (567/4096 : ℝ))) hcmem 8 (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (567/4096 : ℝ)) (991404137093/1000000000000 : ℝ) (123925517137/125000000000 : ℝ) (50756806067/100000000000 : ℝ) (507568060679/1000000000000 : ℝ) (804198828173/1000000000000 : ℝ) (804198828191/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1679_exp_lower
  have heNumeric : (1027503368901/500000000000 : ℝ)/4 ≤ Real.exp (-666015234441/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027503368901/500000000000 : ℝ)/4 ≤ Real.exp ((283/2048 : ℝ)-(804198828191/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (283/2048 : ℝ) (567/4096 : ℝ) (804198828191/1000000000000 : ℝ) (1027503368901/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1680; no trusted numerical premise.
theorem cover8_leaf1680_exp_radius : (498917798828592613/500000000000000000 : ℝ) ≤ Real.exp ((-71/4096 : ℝ)/8) ∧ Real.exp ((-71/4096 : ℝ)/8) ≤ (997835597657185227/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-71/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1680_exp_lower : (230030211862919109/250000000000000000 : ℝ) ≤ Real.exp ((-333001046559/500000000000 : ℝ)/8) ∧ Real.exp ((-333001046559/500000000000 : ℝ)/8) ≤ (920120847451676437/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333001046559/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1680_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055033743487/1000000000000 : ℝ) ≤ 4*Real.exp (567/4096 : ℝ)*Real.exp (-mu (radius 8 (71/512 : ℝ))) ∧ (20549/10000 : ℝ) < (2055033743487/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (71/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1680_exp_radius
  have hrNumeric : (3839122597/3906250000 : ℝ) ≤ Real.exp (-71/4096 : ℝ) ∧ Real.exp (-71/4096 : ℝ) ≤ (982815384833/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (3839122597/3906250000 : ℝ) ≤ (radius 8 (71/512 : ℝ)) ∧ (radius 8 (71/512 : ℝ)) ≤ (982815384833/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (71/512 : ℝ)) (3839122597/3906250000 : ℝ) (982815384833/1000000000000 : ℝ) (9229561113/50000000000 : ℝ) (92295611133/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (71/512 : ℝ)) (3839122597/3906250000 : ℝ) (982815384833/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (71/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (3839122597/3906250000 : ℝ) (982815384833/1000000000000 : ℝ) (7745372597/7812500000 : ℝ) (991407692417/1000000000000 : ℝ) (991370457917/1000000000000 : ℝ) (991370457919/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (71/512 : ℝ)) 1 (7745372597/7812500000 : ℝ) (991407692417/1000000000000 : ℝ) (991370457917/1000000000000 : ℝ) (991370457919/1000000000000 : ℝ) (495694537583/500000000000 : ℝ) (30980908599/31250000000 : ℝ) (991389074991/1000000000000 : ℝ) (495694537497/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (71/512 : ℝ)) 2 (495694537583/500000000000 : ℝ) (30980908599/31250000000 : ℝ) (991389074991/1000000000000 : ℝ) (495694537497/500000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (71/512 : ℝ)) 3 (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (71/512 : ℝ)) 4 (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (71/512 : ℝ)) 5 (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (71/512 : ℝ)) 6 (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (71/512 : ℝ)) 7 (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (71/512 : ℝ))) (9229561113/50000000000 : ℝ) (92295611133/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (71/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (9229561113/50000000000 : ℝ) (92295611133/500000000000 : ℝ) (59229561113/100000000000 : ℝ) (592295611133/1000000000000 : ℝ) (107410201523/250000000000 : ℝ) (4296408061/10000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (71/512 : ℝ))) 1 (59229561113/100000000000 : ℝ) (592295611133/1000000000000 : ℝ) (107410201523/250000000000 : ℝ) (4296408061/10000000000 : ℝ) (510968208611/1000000000000 : ℝ) (510968208617/1000000000000 : ℝ) (126113630263/250000000000 : ℝ) (504454521059/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (71/512 : ℝ))) 2 (510968208611/1000000000000 : ℝ) (510968208617/1000000000000 : ℝ) (126113630263/250000000000 : ℝ) (504454521059/1000000000000 : ℝ) (507711364831/1000000000000 : ℝ) (253855682419/500000000000 : ℝ) (507700918797/1000000000000 : ℝ) (126925229701/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (71/512 : ℝ))) 3 (507711364831/1000000000000 : ℝ) (253855682419/500000000000 : ℝ) (507700918797/1000000000000 : ℝ) (126925229701/250000000000 : ℝ) (253853070907/500000000000 : ℝ) (507706141821/1000000000000 : ℝ) (507706141787/1000000000000 : ℝ) (101541228359/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (71/512 : ℝ))) 4 (253853070907/500000000000 : ℝ) (507706141821/1000000000000 : ℝ) (507706141787/1000000000000 : ℝ) (101541228359/200000000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (71/512 : ℝ))) 5 (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (71/512 : ℝ))) 6 (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (71/512 : ℝ))) 7 (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (71/512 : ℝ)) hmem 8 (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (71/512 : ℝ))) hcmem 8 (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (71/512 : ℝ)) (495694537539/500000000000 : ℝ) (991389075081/1000000000000 : ℝ) (2538530709/5000000000 : ℝ) (31731633863/62500000000 : ℝ) (804429827477/1000000000000 : ℝ) (804429827493/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1680_exp_lower
  have heNumeric : (2055033743487/1000000000000 : ℝ)/4 ≤ Real.exp (-333001046559/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055033743487/1000000000000 : ℝ)/4 ≤ Real.exp ((567/4096 : ℝ)-(804429827493/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (567/4096 : ℝ) (71/512 : ℝ) (804429827493/1000000000000 : ℝ) (2055033743487/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1681; no trusted numerical premise.
theorem cover8_leaf1681_exp_radius : (1995663582447439/2000000000000000 : ℝ) ≤ Real.exp ((-569/32768 : ℝ)/8) ∧ Real.exp ((-569/32768 : ℝ)/8) ≤ (997831791223719501/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-569/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1681_exp_lower : (920122390411325241/1000000000000000000 : ℝ) ≤ Real.exp ((-665988677851/1000000000000 : ℝ)/8) ∧ Real.exp ((-665988677851/1000000000000 : ℝ)/8) ≤ (460061195205662621/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665988677851/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1681_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027530656249/500000000000 : ℝ) ≤ 4*Real.exp (71/512 : ℝ)*Real.exp (-mu (radius 8 (569/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027530656249/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (569/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1681_exp_radius
  have hrNumeric : (61424087009/62500000000 : ℝ) ≤ Real.exp (-569/32768 : ℝ) ∧ Real.exp (-569/32768 : ℝ) ≤ (196557078429/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61424087009/62500000000 : ℝ) ≤ (radius 8 (569/4096 : ℝ)) ∧ (radius 8 (569/4096 : ℝ)) ≤ (196557078429/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (569/4096 : ℝ)) (61424087009/62500000000 : ℝ) (196557078429/200000000000 : ℝ) (92375420143/500000000000 : ℝ) (46187710073/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (569/4096 : ℝ)) (61424087009/62500000000 : ℝ) (196557078429/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (569/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61424087009/62500000000 : ℝ) (196557078429/200000000000 : ℝ) (123924087009/125000000000 : ℝ) (991392696073/1000000000000 : ℝ) (24783883273/25000000000 : ℝ) (991355330921/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (569/4096 : ℝ)) 1 (123924087009/125000000000 : ℝ) (991392696073/1000000000000 : ℝ) (24783883273/25000000000 : ℝ) (991355330921/1000000000000 : ℝ) (123921751687/125000000000 : ℝ) (991374013497/1000000000000 : ℝ) (991374013319/1000000000000 : ℝ) (991374013321/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (569/4096 : ℝ)) 2 (123921751687/125000000000 : ℝ) (991374013497/1000000000000 : ℝ) (991374013319/1000000000000 : ℝ) (991374013321/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (569/4096 : ℝ)) 3 (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (569/4096 : ℝ)) 4 (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (569/4096 : ℝ)) 5 (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (569/4096 : ℝ)) 6 (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (569/4096 : ℝ)) 7 (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (569/4096 : ℝ))) (92375420143/500000000000 : ℝ) (46187710073/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (569/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (92375420143/500000000000 : ℝ) (46187710073/250000000000 : ℝ) (592375420143/1000000000000 : ℝ) (296187710073/500000000000 : ℝ) (214913261739/500000000000 : ℝ) (214913261743/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (569/4096 : ℝ))) 1 (592375420143/1000000000000 : ℝ) (296187710073/500000000000 : ℝ) (214913261739/500000000000 : ℝ) (214913261743/500000000000 : ℝ) (51110097181/100000000000 : ℝ) (63887621477/125000000000 : ℝ) (10091950603/20000000000 : ℝ) (504597530157/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (569/4096 : ℝ))) 2 (51110097181/100000000000 : ℝ) (63887621477/125000000000 : ℝ) (10091950603/20000000000 : ℝ) (504597530157/1000000000000 : ℝ) (25392462549/50000000000 : ℝ) (507849250987/1000000000000 : ℝ) (50783884061/100000000000 : ℝ) (507838840617/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (569/4096 : ℝ))) 3 (25392462549/50000000000 : ℝ) (507849250987/1000000000000 : ℝ) (50783884061/100000000000 : ℝ) (507838840617/1000000000000 : ℝ) (101568809159/200000000000 : ℝ) (253922022901/500000000000 : ℝ) (63480505721/125000000000 : ℝ) (31740252861/62500000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (569/4096 : ℝ))) 4 (101568809159/200000000000 : ℝ) (253922022901/500000000000 : ℝ) (63480505721/125000000000 : ℝ) (31740252861/62500000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (569/4096 : ℝ))) 5 (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (569/4096 : ℝ))) 6 (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (569/4096 : ℝ))) 7 (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (569/4096 : ℝ)) hmem 8 (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (569/4096 : ℝ))) hcmem 8 (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (569/4096 : ℝ)) (991374013407/1000000000000 : ℝ) (991374013409/1000000000000 : ℝ) (507844045781/1000000000000 : ℝ) (507844045789/1000000000000 : ℝ) (201165138209/250000000000 : ℝ) (804660552851/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1681_exp_lower
  have heNumeric : (1027530656249/500000000000 : ℝ)/4 ≤ Real.exp (-665988677851/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027530656249/500000000000 : ℝ)/4 ≤ Real.exp ((71/512 : ℝ)-(804660552851/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (71/512 : ℝ) (569/4096 : ℝ) (804660552851/1000000000000 : ℝ) (1027530656249/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1682; no trusted numerical premise.
theorem cover8_leaf1682_exp_radius : (498913992402387069/500000000000000000 : ℝ) ≤ Real.exp ((-285/16384 : ℝ)/8) ∧ Real.exp ((-285/16384 : ℝ)/8) ≤ (997827984804774139/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-285/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1682_exp_lower : (9201239647853279/10000000000000000 : ℝ) ≤ Real.exp ((-26638999579/40000000000 : ℝ)/8) ∧ Real.exp ((-26638999579/40000000000 : ℝ)/8) ≤ (920123964785327901/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-26638999579/40000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1682_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055089443143/1000000000000 : ℝ) ≤ 4*Real.exp (569/4096 : ℝ)*Real.exp (-mu (radius 8 (285/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055089443143/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (285/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1682_exp_radius
  have hrNumeric : (245688850093/250000000000 : ℝ) ≤ Real.exp (-285/16384 : ℝ) ∧ Real.exp (-285/16384 : ℝ) ≤ (982755400373/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245688850093/250000000000 : ℝ) ≤ (radius 8 (285/2048 : ℝ)) ∧ (radius 8 (285/2048 : ℝ)) ≤ (982755400373/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (285/2048 : ℝ)) (245688850093/250000000000 : ℝ) (982755400373/1000000000000 : ℝ) (184910310793/1000000000000 : ℝ) (184910310799/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (285/2048 : ℝ)) (245688850093/250000000000 : ℝ) (982755400373/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (285/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245688850093/250000000000 : ℝ) (982755400373/1000000000000 : ℝ) (495688850093/500000000000 : ℝ) (991377700187/1000000000000 : ℝ) (991340204153/1000000000000 : ℝ) (198268040831/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (285/2048 : ℝ)) 1 (495688850093/500000000000 : ℝ) (991377700187/1000000000000 : ℝ) (991340204153/1000000000000 : ℝ) (198268040831/200000000000 : ℝ) (991358952169/1000000000000 : ℝ) (991358952171/1000000000000 : ℝ) (123919868999/125000000000 : ℝ) (495679475997/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (285/2048 : ℝ)) 2 (991358952169/1000000000000 : ℝ) (991358952171/1000000000000 : ℝ) (123919868999/125000000000 : ℝ) (495679475997/500000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (285/2048 : ℝ)) 3 (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (285/2048 : ℝ)) 4 (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (285/2048 : ℝ)) 5 (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (285/2048 : ℝ)) 6 (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (285/2048 : ℝ)) 7 (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (285/2048 : ℝ))) (184910310793/1000000000000 : ℝ) (184910310799/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (285/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (184910310793/1000000000000 : ℝ) (184910310799/1000000000000 : ℝ) (148113788849/250000000000 : ℝ) (2962275777/5000000000 : ℝ) (430011989127/1000000000000 : ℝ) (86002397827/200000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (285/2048 : ℝ))) 1 (148113788849/250000000000 : ℝ) (2962275777/5000000000 : ℝ) (430011989127/1000000000000 : ℝ) (86002397827/200000000000 : ℝ) (511233572261/1000000000000 : ℝ) (127808393067/250000000000 : ℝ) (126185087233/250000000000 : ℝ) (504740348939/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (285/2048 : ℝ))) 2 (511233572261/1000000000000 : ℝ) (127808393067/250000000000 : ℝ) (126185087233/250000000000 : ℝ) (504740348939/1000000000000 : ℝ) (126996740149/250000000000 : ℝ) (126996740151/250000000000 : ℝ) (992141769/1953125000 : ℝ) (63497073217/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (285/2048 : ℝ))) 3 (126996740149/250000000000 : ℝ) (126996740151/250000000000 : ℝ) (992141769/1953125000 : ℝ) (63497073217/125000000000 : ℝ) (253990886581/500000000000 : ℝ) (50798177317/100000000000 : ℝ) (101596354627/200000000000 : ℝ) (63497721643/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (285/2048 : ℝ))) 4 (253990886581/500000000000 : ℝ) (50798177317/100000000000 : ℝ) (101596354627/200000000000 : ℝ) (63497721643/125000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (285/2048 : ℝ))) 5 (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (285/2048 : ℝ))) 6 (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (285/2048 : ℝ))) 7 (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (285/2048 : ℝ)) hmem 8 (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (285/2048 : ℝ))) hcmem 8 (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (285/2048 : ℝ)) (12391986901/12500000000 : ℝ) (991358952083/1000000000000 : ℝ) (126995443287/250000000000 : ℝ) (507981773157/1000000000000 : ℝ) (402445502541/500000000000 : ℝ) (8048910051/10000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1682_exp_lower
  have heNumeric : (2055089443143/1000000000000 : ℝ)/4 ≤ Real.exp (-26638999579/40000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055089443143/1000000000000 : ℝ)/4 ≤ Real.exp ((569/4096 : ℝ)-(8048910051/10000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (569/4096 : ℝ) (285/2048 : ℝ) (8048910051/10000000000 : ℝ) (2055089443143/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1683; no trusted numerical premise.
theorem cover8_leaf1683_exp_radius : (249456044600087271/250000000000000000 : ℝ) ≤ Real.exp ((-571/32768 : ℝ)/8) ∧ Real.exp ((-571/32768 : ℝ)/8) ≤ (199564835680069817/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-571/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1683_exp_lower : (460062785238328699/500000000000000000 : ℝ) ≤ Real.exp ((-133192205767/200000000000 : ℝ)/8) ∧ Real.exp ((-133192205767/200000000000 : ℝ)/8) ≤ (920125570476657399/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133192205767/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1683_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055118133707/1000000000000 : ℝ) ≤ 4*Real.exp (285/2048 : ℝ)*Real.exp (-mu (radius 8 (571/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2055118133707/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (571/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1683_exp_radius
  have hrNumeric : (196545081903/200000000000 : ℝ) ≤ Real.exp (-571/32768 : ℝ) ∧ Real.exp (-571/32768 : ℝ) ≤ (245681352379/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196545081903/200000000000 : ℝ) ≤ (radius 8 (571/4096 : ℝ)) ∧ (radius 8 (571/4096 : ℝ)) ≤ (245681352379/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (571/4096 : ℝ)) (196545081903/200000000000 : ℝ) (245681352379/250000000000 : ℝ) (185069634169/1000000000000 : ℝ) (7402785367/40000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (571/4096 : ℝ)) (196545081903/200000000000 : ℝ) (245681352379/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (571/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196545081903/200000000000 : ℝ) (245681352379/250000000000 : ℝ) (991362704757/1000000000000 : ℝ) (495681352379/500000000000 : ℝ) (495662538809/500000000000 : ℝ) (991325077619/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (571/4096 : ℝ)) 1 (991362704757/1000000000000 : ℝ) (495681352379/500000000000 : ℝ) (495662538809/500000000000 : ℝ) (991325077619/1000000000000 : ℝ) (991343891187/1000000000000 : ℝ) (991343891189/1000000000000 : ℝ) (15489748297/15625000000 : ℝ) (99134389101/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (571/4096 : ℝ)) 2 (991343891187/1000000000000 : ℝ) (991343891189/1000000000000 : ℝ) (15489748297/15625000000 : ℝ) (99134389101/100000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (571/4096 : ℝ)) 3 (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (571/4096 : ℝ)) 4 (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (571/4096 : ℝ)) 5 (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (571/4096 : ℝ)) 6 (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (571/4096 : ℝ)) 7 (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (571/4096 : ℝ))) (185069634169/1000000000000 : ℝ) (7402785367/40000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (571/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (185069634169/1000000000000 : ℝ) (7402785367/40000000000 : ℝ) (148133704271/250000000000 : ℝ) (9258356517/15625000000 : ℝ) (430197203813/1000000000000 : ℝ) (430197203821/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (571/4096 : ℝ))) 1 (148133704271/250000000000 : ℝ) (9258356517/15625000000 : ℝ) (430197203813/1000000000000 : ℝ) (430197203821/1000000000000 : ℝ) (31960375653/62500000000 : ℝ) (102273202091/200000000000 : ℝ) (504882977997/1000000000000 : ℝ) (126220744501/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (571/4096 : ℝ))) 2 (31960375653/62500000000 : ℝ) (102273202091/200000000000 : ℝ) (504882977997/1000000000000 : ℝ) (126220744501/250000000000 : ℝ) (254062247111/500000000000 : ℝ) (50812449423/100000000000 : ℝ) (101622830939/200000000000 : ℝ) (508114154703/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (571/4096 : ℝ))) 3 (254062247111/500000000000 : ℝ) (50812449423/100000000000 : ℝ) (101622830939/200000000000 : ℝ) (508114154703/1000000000000 : ℝ) (254059662229/500000000000 : ℝ) (508119324467/1000000000000 : ℝ) (31757457777/62500000000 : ℝ) (508119324441/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (571/4096 : ℝ))) 4 (254059662229/500000000000 : ℝ) (508119324467/1000000000000 : ℝ) (31757457777/62500000000 : ℝ) (508119324441/1000000000000 : ℝ) (101623864889/200000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (571/4096 : ℝ))) 5 (101623864889/200000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (571/4096 : ℝ))) 6 (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (571/4096 : ℝ))) 7 (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (571/4096 : ℝ)) hmem 8 (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (571/4096 : ℝ))) hcmem 8 (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (571/4096 : ℝ)) (991343891097/1000000000000 : ℝ) (9913438911/10000000000 : ℝ) (127029831111/250000000000 : ℝ) (254059662227/500000000000 : ℝ) (161024237013/200000000000 : ℝ) (161024237017/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1683_exp_lower
  have heNumeric : (2055118133707/1000000000000 : ℝ)/4 ≤ Real.exp (-133192205767/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055118133707/1000000000000 : ℝ)/4 ≤ Real.exp ((285/2048 : ℝ)-(161024237017/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (285/2048 : ℝ) (571/4096 : ℝ) (161024237017/200000000000 : ℝ) (2055118133707/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1684; no trusted numerical premise.
theorem cover8_leaf1684_exp_radius : (997820372010444283/1000000000000000000 : ℝ) ≤ Real.exp ((-143/8192 : ℝ)/8) ∧ Real.exp ((-143/8192 : ℝ)/8) ≤ (249455093002611071/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-143/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1684_exp_lower : (920127207389784447/1000000000000000000 : ℝ) ≤ Real.exp ((-665946796763/1000000000000 : ℝ)/8) ∧ Real.exp ((-665946796763/1000000000000 : ℝ)/8) ≤ (7188493807732691/7812500000000000 : ℝ) := by
  have h := exp_small_bounds ((-665946796763/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1684_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256893422813/125000000000 : ℝ) ≤ 4*Real.exp (571/4096 : ℝ)*Real.exp (-mu (radius 8 (143/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (256893422813/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (143/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1684_exp_radius
  have hrNumeric : (982695419573/1000000000000 : ℝ) ≤ Real.exp (-143/8192 : ℝ) ∧ Real.exp (-143/8192 : ℝ) ≤ (491347709787/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982695419573/1000000000000 : ℝ) ≤ (radius 8 (143/1024 : ℝ)) ∧ (radius 8 (143/1024 : ℝ)) ≤ (491347709787/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (143/1024 : ℝ)) (982695419573/1000000000000 : ℝ) (491347709787/500000000000 : ℝ) (92614405397/500000000000 : ℝ) (463072027/2500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (143/1024 : ℝ)) (982695419573/1000000000000 : ℝ) (491347709787/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (143/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982695419573/1000000000000 : ℝ) (491347709787/500000000000 : ℝ) (495673854893/500000000000 : ℝ) (991347709787/1000000000000 : ℝ) (991309951313/1000000000000 : ℝ) (495654975657/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (143/1024 : ℝ)) 1 (495673854893/500000000000 : ℝ) (991347709787/1000000000000 : ℝ) (991309951313/1000000000000 : ℝ) (495654975657/500000000000 : ℝ) (991328830549/1000000000000 : ℝ) (991328830551/1000000000000 : ℝ) (991328830369/1000000000000 : ℝ) (991328830371/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (143/1024 : ℝ)) 2 (991328830549/1000000000000 : ℝ) (991328830551/1000000000000 : ℝ) (991328830369/1000000000000 : ℝ) (991328830371/1000000000000 : ℝ) (991328830459/1000000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (143/1024 : ℝ)) 3 (991328830459/1000000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (143/1024 : ℝ)) 4 (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (143/1024 : ℝ)) 5 (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (143/1024 : ℝ)) 6 (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (143/1024 : ℝ)) 7 (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (143/1024 : ℝ))) (92614405397/500000000000 : ℝ) (463072027/2500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (143/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (92614405397/500000000000 : ℝ) (463072027/2500000000 : ℝ) (592614405397/1000000000000 : ℝ) (2963072027/5000000000 : ℝ) (430382168303/1000000000000 : ℝ) (430382168311/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (143/1024 : ℝ))) 1 (592614405397/1000000000000 : ℝ) (2963072027/5000000000 : ℝ) (430382168303/1000000000000 : ℝ) (430382168311/1000000000000 : ℝ) (10229965737/20000000000 : ℝ) (63937285857/125000000000 : ℝ) (31564088621/62500000000 : ℝ) (505025417943/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (143/1024 : ℝ))) 2 (10229965737/20000000000 : ℝ) (63937285857/125000000000 : ℝ) (31564088621/62500000000 : ℝ) (505025417943/1000000000000 : ℝ) (508261852393/1000000000000 : ℝ) (1270654631/2500000000 : ℝ) (127062887011/250000000000 : ℝ) (127062887013/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (143/1024 : ℝ))) 3 (508261852393/1000000000000 : ℝ) (1270654631/2500000000 : ℝ) (127062887011/250000000000 : ℝ) (127062887013/250000000000 : ℝ) (254128350109/500000000000 : ℝ) (254128350113/500000000000 : ℝ) (15883021881/31250000000 : ℝ) (2541283501/5000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (143/1024 : ℝ))) 4 (254128350109/500000000000 : ℝ) (254128350113/500000000000 : ℝ) (15883021881/31250000000 : ℝ) (2541283501/5000000000 : ℝ) (101651340041/200000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (143/1024 : ℝ))) 5 (101651340041/200000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (143/1024 : ℝ))) 6 (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (143/1024 : ℝ))) 7 (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (143/1024 : ℝ)) hmem 8 (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (143/1024 : ℝ))) hcmem 8 (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (143/1024 : ℝ)) (495664415229/500000000000 : ℝ) (991328830461/1000000000000 : ℝ) (127064175051/250000000000 : ℝ) (508256700213/1000000000000 : ℝ) (40267554681/50000000000 : ℝ) (402675546819/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1684_exp_lower
  have heNumeric : (256893422813/125000000000 : ℝ)/4 ≤ Real.exp (-665946796763/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256893422813/125000000000 : ℝ)/4 ≤ Real.exp ((571/4096 : ℝ)-(402675546819/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (571/4096 : ℝ) (143/1024 : ℝ) (402675546819/500000000000 : ℝ) (256893422813/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1685; no trusted numerical premise.
theorem cover8_leaf1685_exp_radius : (997816565635059679/1000000000000000000 : ℝ) ≤ Real.exp ((-573/32768 : ℝ)/8) ∧ Real.exp ((-573/32768 : ℝ)/8) ≤ (6236353535219123/6250000000000000 : ℝ) := by
  have h := exp_small_bounds ((-573/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1685_exp_lower : (460064437714361101/500000000000000000 : ℝ) ≤ Real.exp ((-133186458819/200000000000 : ℝ)/8) ∧ Real.exp ((-133186458819/200000000000 : ℝ)/8) ≤ (920128875428722203/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-133186458819/200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1685_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (802803589/390625000 : ℝ) ≤ 4*Real.exp (143/1024 : ℝ)*Real.exp (-mu (radius 8 (573/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (802803589/390625000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (573/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1685_exp_radius
  have hrNumeric : (491332715273/500000000000 : ℝ) ≤ Real.exp (-573/32768 : ℝ) ∧ Real.exp (-573/32768 : ℝ) ≤ (982665430547/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491332715273/500000000000 : ℝ) ≤ (radius 8 (573/4096 : ℝ)) ∧ (radius 8 (573/4096 : ℝ)) ≤ (982665430547/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (573/4096 : ℝ)) (491332715273/500000000000 : ℝ) (982665430547/1000000000000 : ℝ) (92693920523/500000000000 : ℝ) (46346960263/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (573/4096 : ℝ)) (491332715273/500000000000 : ℝ) (982665430547/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (573/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491332715273/500000000000 : ℝ) (982665430547/1000000000000 : ℝ) (991332715273/1000000000000 : ℝ) (495666357637/500000000000 : ℝ) (991294825239/1000000000000 : ℝ) (24782370631/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (573/4096 : ℝ)) 1 (991332715273/1000000000000 : ℝ) (495666357637/500000000000 : ℝ) (991294825239/1000000000000 : ℝ) (24782370631/25000000000 : ℝ) (61957110641/62500000000 : ℝ) (991313770257/1000000000000 : ℝ) (495656885037/500000000000 : ℝ) (247828442519/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (573/4096 : ℝ)) 2 (61957110641/62500000000 : ℝ) (991313770257/1000000000000 : ℝ) (495656885037/500000000000 : ℝ) (247828442519/250000000000 : ℝ) (198262754033/200000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (573/4096 : ℝ)) 3 (198262754033/200000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (573/4096 : ℝ)) 4 (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (573/4096 : ℝ)) 5 (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (573/4096 : ℝ)) 6 (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (573/4096 : ℝ)) 7 (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (573/4096 : ℝ))) (92693920523/500000000000 : ℝ) (46346960263/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (573/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (92693920523/500000000000 : ℝ) (46346960263/250000000000 : ℝ) (592693920523/1000000000000 : ℝ) (296346960263/500000000000 : ℝ) (430566883359/1000000000000 : ℝ) (430566883367/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (573/4096 : ℝ))) 1 (592693920523/1000000000000 : ℝ) (296346960263/500000000000 : ℝ) (430566883359/1000000000000 : ℝ) (430566883367/1000000000000 : ℝ) (511630401941/1000000000000 : ℝ) (511630401947/1000000000000 : ℝ) (505167669339/1000000000000 : ℝ) (101033533869/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (573/4096 : ℝ))) 2 (511630401941/1000000000000 : ℝ) (511630401947/1000000000000 : ℝ) (505167669339/1000000000000 : ℝ) (101033533869/200000000000 : ℝ) (12709975891/25000000000 : ℝ) (254199517823/500000000000 : ℝ) (508388766311/1000000000000 : ℝ) (254194383159/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (573/4096 : ℝ))) 3 (12709975891/25000000000 : ℝ) (254199517823/500000000000 : ℝ) (508388766311/1000000000000 : ℝ) (254194383159/500000000000 : ℝ) (20335756039/40000000000 : ℝ) (254196950491/500000000000 : ℝ) (508393900949/1000000000000 : ℝ) (508393900957/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (573/4096 : ℝ))) 4 (20335756039/40000000000 : ℝ) (254196950491/500000000000 : ℝ) (508393900949/1000000000000 : ℝ) (508393900957/1000000000000 : ℝ) (254196950481/500000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (573/4096 : ℝ))) 5 (254196950481/500000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (573/4096 : ℝ))) 6 (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (573/4096 : ℝ))) 7 (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (573/4096 : ℝ)) hmem 8 (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (573/4096 : ℝ))) hcmem 8 (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (573/4096 : ℝ)) (247828442541/250000000000 : ℝ) (991313770167/1000000000000 : ℝ) (508393900961/1000000000000 : ℝ) (50839390097/100000000000 : ℝ) (805580731577/1000000000000 : ℝ) (161116146319/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1685_exp_lower
  have heNumeric : (802803589/390625000 : ℝ)/4 ≤ Real.exp (-133186458819/200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (802803589/390625000 : ℝ)/4 ≤ Real.exp ((143/1024 : ℝ)-(161116146319/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (143/1024 : ℝ) (573/4096 : ℝ) (161116146319/200000000000 : ℝ) (802803589/390625000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1686; no trusted numerical premise.
theorem cover8_leaf1686_exp_radius : (498906379637097609/500000000000000000 : ℝ) ≤ Real.exp ((-287/16384 : ℝ)/8) ∧ Real.exp ((-287/16384 : ℝ)/8) ≤ (997812759274195219/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-287/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1686_exp_lower : (46006528724977829/50000000000000000 : ℝ) ≤ Real.exp ((-665917521649/1000000000000 : ℝ)/8) ∧ Real.exp ((-665917521649/1000000000000 : ℝ)/8) ≤ (920130574499556581/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665917521649/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1686_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055207548059/1000000000000 : ℝ) ≤ 4*Real.exp (573/4096 : ℝ)*Real.exp (-mu (radius 8 (287/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055207548059/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (287/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1686_exp_radius
  have hrNumeric : (196527088487/200000000000 : ℝ) ≤ Real.exp (-287/16384 : ℝ) ∧ Real.exp (-287/16384 : ℝ) ≤ (245658860609/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (196527088487/200000000000 : ℝ) ≤ (radius 8 (287/2048 : ℝ)) ∧ (radius 8 (287/2048 : ℝ)) ≤ (245658860609/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (287/2048 : ℝ)) (196527088487/200000000000 : ℝ) (245658860609/250000000000 : ℝ) (185546725297/1000000000000 : ℝ) (185546725303/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (287/2048 : ℝ)) (196527088487/200000000000 : ℝ) (245658860609/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (287/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (196527088487/200000000000 : ℝ) (245658860609/250000000000 : ℝ) (991317721217/1000000000000 : ℝ) (495658860609/500000000000 : ℝ) (247819924849/250000000000 : ℝ) (991279699397/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (287/2048 : ℝ)) 1 (991317721217/1000000000000 : ℝ) (495658860609/500000000000 : ℝ) (247819924849/250000000000 : ℝ) (991279699397/1000000000000 : ℝ) (495649355153/500000000000 : ℝ) (247824677577/250000000000 : ℝ) (247824677531/250000000000 : ℝ) (495649355063/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (287/2048 : ℝ)) 2 (495649355153/500000000000 : ℝ) (247824677577/250000000000 : ℝ) (247824677531/250000000000 : ℝ) (495649355063/500000000000 : ℝ) (198259742043/200000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (287/2048 : ℝ)) 3 (198259742043/200000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (287/2048 : ℝ)) 4 (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (287/2048 : ℝ)) 5 (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (287/2048 : ℝ)) 6 (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (287/2048 : ℝ)) 7 (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (287/2048 : ℝ))) (185546725297/1000000000000 : ℝ) (185546725303/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (287/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (185546725297/1000000000000 : ℝ) (185546725303/1000000000000 : ℝ) (74096670331/125000000000 : ℝ) (148193340663/250000000000 : ℝ) (430751349733/1000000000000 : ℝ) (430751349741/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (287/2048 : ℝ))) 1 (74096670331/125000000000 : ℝ) (148193340663/250000000000 : ℝ) (430751349733/1000000000000 : ℝ) (430751349741/1000000000000 : ℝ) (51176235619/100000000000 : ℝ) (511762356197/1000000000000 : ℝ) (31581858299/62500000000 : ℝ) (505309732791/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (287/2048 : ℝ))) 2 (51176235619/100000000000 : ℝ) (511762356197/1000000000000 : ℝ) (31581858299/62500000000 : ℝ) (505309732791/1000000000000 : ℝ) (508536044487/1000000000000 : ℝ) (254268022247/500000000000 : ℝ) (254262905009/500000000000 : ℝ) (254262905013/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (287/2048 : ℝ))) 3 (508536044487/1000000000000 : ℝ) (254268022247/500000000000 : ℝ) (254262905009/500000000000 : ℝ) (254262905013/500000000000 : ℝ) (127132731813/250000000000 : ℝ) (25426546363/50000000000 : ℝ) (254265463613/500000000000 : ℝ) (101706185447/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (287/2048 : ℝ))) 4 (127132731813/250000000000 : ℝ) (25426546363/50000000000 : ℝ) (254265463613/500000000000 : ℝ) (101706185447/200000000000 : ℝ) (508530927239/1000000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (287/2048 : ℝ))) 5 (508530927239/1000000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (287/2048 : ℝ))) 6 (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (287/2048 : ℝ))) 7 (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (287/2048 : ℝ)) hmem 8 (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (287/2048 : ℝ))) hcmem 8 (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (287/2048 : ℝ)) (495649355107/500000000000 : ℝ) (991298710217/1000000000000 : ℝ) (254265463619/500000000000 : ℝ) (31783182953/62500000000 : ℝ) (161162019951/200000000000 : ℝ) (402905049887/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1686_exp_lower
  have heNumeric : (2055207548059/1000000000000 : ℝ)/4 ≤ Real.exp (-665917521649/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055207548059/1000000000000 : ℝ)/4 ≤ Real.exp ((573/4096 : ℝ)-(402905049887/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (573/4096 : ℝ) (287/2048 : ℝ) (402905049887/500000000000 : ℝ) (2055207548059/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1687; no trusted numerical premise.
theorem cover8_leaf1687_exp_radius : (997808952927850843/1000000000000000000 : ℝ) ≤ Real.exp ((-575/32768 : ℝ)/8) ∧ Real.exp ((-575/32768 : ℝ)/8) ≤ (249452238231962711/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-575/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1687_exp_lower : (460066152253612891/500000000000000000 : ℝ) ≤ Real.exp ((-665902480253/1000000000000 : ℝ)/8) ∧ Real.exp ((-665902480253/1000000000000 : ℝ)/8) ≤ (920132304507225783/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665902480253/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1687_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027619230741/500000000000 : ℝ) ≤ 4*Real.exp (287/2048 : ℝ)*Real.exp (-mu (radius 8 (575/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (1027619230741/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (575/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1687_exp_radius
  have hrNumeric : (982605455239/1000000000000 : ℝ) ≤ Real.exp (-575/32768 : ℝ) ∧ Real.exp (-575/32768 : ℝ) ≤ (24565136381/25000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982605455239/1000000000000 : ℝ) ≤ (radius 8 (575/4096 : ℝ)) ∧ (radius 8 (575/4096 : ℝ)) ≤ (24565136381/25000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (575/4096 : ℝ)) (982605455239/1000000000000 : ℝ) (24565136381/25000000000 : ℝ) (185705463927/1000000000000 : ℝ) (185705463933/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (575/4096 : ℝ)) (982605455239/1000000000000 : ℝ) (24565136381/25000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (575/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982605455239/1000000000000 : ℝ) (24565136381/25000000000 : ℝ) (991302727619/1000000000000 : ℝ) (49565136381/50000000000 : ℝ) (991264573783/1000000000000 : ℝ) (198252914757/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (575/4096 : ℝ)) 1 (991302727619/1000000000000 : ℝ) (49565136381/50000000000 : ℝ) (991264573783/1000000000000 : ℝ) (198252914757/200000000000 : ℝ) (991283650701/1000000000000 : ℝ) (991283650703/1000000000000 : ℝ) (991283650517/1000000000000 : ℝ) (991283650519/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (575/4096 : ℝ)) 2 (991283650701/1000000000000 : ℝ) (991283650703/1000000000000 : ℝ) (991283650517/1000000000000 : ℝ) (991283650519/1000000000000 : ℝ) (991283650609/1000000000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (575/4096 : ℝ)) 3 (991283650609/1000000000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (575/4096 : ℝ)) 4 (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (575/4096 : ℝ)) 5 (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (575/4096 : ℝ)) 6 (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (575/4096 : ℝ)) 7 (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (575/4096 : ℝ))) (185705463927/1000000000000 : ℝ) (185705463933/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (575/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (185705463927/1000000000000 : ℝ) (185705463933/1000000000000 : ℝ) (592852731963/1000000000000 : ℝ) (592852731967/1000000000000 : ℝ) (86187113637/200000000000 : ℝ) (430935568193/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (575/4096 : ℝ))) 1 (592852731963/1000000000000 : ℝ) (592852731967/1000000000000 : ℝ) (86187113637/200000000000 : ℝ) (430935568193/1000000000000 : ℝ) (255947075037/500000000000 : ℝ) (1599669219/3125000000 : ℝ) (505451608859/1000000000000 : ℝ) (252725804433/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (575/4096 : ℝ))) 2 (255947075037/500000000000 : ℝ) (1599669219/3125000000 : ℝ) (505451608859/1000000000000 : ℝ) (252725804433/500000000000 : ℝ) (254336439733/500000000000 : ℝ) (508672879473/1000000000000 : ℝ) (5086626797/10000000000 : ℝ) (127165669927/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (575/4096 : ℝ))) 3 (254336439733/500000000000 : ℝ) (508672879473/1000000000000 : ℝ) (5086626797/10000000000 : ℝ) (127165669927/250000000000 : ℝ) (508667779583/1000000000000 : ℝ) (508667779591/1000000000000 : ℝ) (508667779557/1000000000000 : ℝ) (101733555913/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (575/4096 : ℝ))) 4 (508667779583/1000000000000 : ℝ) (508667779591/1000000000000 : ℝ) (508667779557/1000000000000 : ℝ) (101733555913/200000000000 : ℝ) (50866777957/100000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (575/4096 : ℝ))) 5 (50866777957/100000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (575/4096 : ℝ))) 6 (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (575/4096 : ℝ))) 7 (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (575/4096 : ℝ)) hmem 8 (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (575/4096 : ℝ))) hcmem 8 (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (575/4096 : ℝ)) (61955228163/62500000000 : ℝ) (991283650611/1000000000000 : ℝ) (508667779569/1000000000000 : ℝ) (254333889789/500000000000 : ℝ) (161207839797/200000000000 : ℝ) (806039199003/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1687_exp_lower
  have heNumeric : (1027619230741/500000000000 : ℝ)/4 ≤ Real.exp (-665902480253/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027619230741/500000000000 : ℝ)/4 ≤ Real.exp ((287/2048 : ℝ)-(806039199003/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (287/2048 : ℝ) (575/4096 : ℝ) (806039199003/1000000000000 : ℝ) (1027619230741/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1688; no trusted numerical premise.
theorem cover8_leaf1688_exp_radius : (997805146596026499/1000000000000000000 : ℝ) ≤ Real.exp ((-9/512 : ℝ)/8) ∧ Real.exp ((-9/512 : ℝ)/8) ≤ (1995610293192053/2000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-9/512 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1688_exp_lower : (920134065356440387/1000000000000000000 : ℝ) ≤ Real.exp ((-665887170737/1000000000000 : ℝ)/8) ∧ Real.exp ((-665887170737/1000000000000 : ℝ)/8) ≤ (230033516339110097/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665887170737/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1688_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055269926429/1000000000000 : ℝ) ≤ 4*Real.exp (575/4096 : ℝ)*Real.exp (-mu (radius 8 (9/64 : ℝ))) ∧ (20549/10000 : ℝ) < (2055269926429/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (9/64 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1688_exp_radius
  have hrNumeric : (982575468957/1000000000000 : ℝ) ≤ Real.exp (-9/512 : ℝ) ∧ Real.exp (-9/512 : ℝ) ≤ (491287734479/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982575468957/1000000000000 : ℝ) ≤ (radius 8 (9/64 : ℝ)) ∧ (radius 8 (9/64 : ℝ)) ≤ (491287734479/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (9/64 : ℝ)) (982575468957/1000000000000 : ℝ) (491287734479/500000000000 : ℝ) (46466014329/250000000000 : ℝ) (92932028661/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (9/64 : ℝ)) (982575468957/1000000000000 : ℝ) (491287734479/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (9/64 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982575468957/1000000000000 : ℝ) (491287734479/500000000000 : ℝ) (495643867239/500000000000 : ℝ) (991287734479/1000000000000 : ℝ) (991249448401/1000000000000 : ℝ) (991249448403/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (9/64 : ℝ)) 1 (495643867239/500000000000 : ℝ) (991287734479/1000000000000 : ℝ) (991249448401/1000000000000 : ℝ) (991249448403/1000000000000 : ℝ) (991268591439/1000000000000 : ℝ) (991268591441/1000000000000 : ℝ) (495634295627/500000000000 : ℝ) (991268591257/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (9/64 : ℝ)) 2 (991268591439/1000000000000 : ℝ) (991268591441/1000000000000 : ℝ) (495634295627/500000000000 : ℝ) (991268591257/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (9/64 : ℝ)) 3 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (9/64 : ℝ)) 4 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (9/64 : ℝ)) 5 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (9/64 : ℝ)) 6 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (9/64 : ℝ)) 7 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (9/64 : ℝ))) (46466014329/250000000000 : ℝ) (92932028661/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (9/64 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (46466014329/250000000000 : ℝ) (92932028661/500000000000 : ℝ) (296466014329/500000000000 : ℝ) (592932028661/1000000000000 : ℝ) (431119539473/1000000000000 : ℝ) (431119539481/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (9/64 : ℝ))) 1 (296466014329/500000000000 : ℝ) (592932028661/1000000000000 : ℝ) (431119539473/1000000000000 : ℝ) (431119539481/1000000000000 : ℝ) (102405156813/200000000000 : ℝ) (512025784071/1000000000000 : ℝ) (505593298149/1000000000000 : ℝ) (126398324539/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (9/64 : ℝ))) 2 (102405156813/200000000000 : ℝ) (512025784071/1000000000000 : ℝ) (505593298149/1000000000000 : ℝ) (126398324539/250000000000 : ℝ) (508809541107/1000000000000 : ℝ) (254404770557/500000000000 : ℝ) (254399687943/500000000000 : ℝ) (254399687947/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (9/64 : ℝ))) 3 (508809541107/1000000000000 : ℝ) (254404770557/500000000000 : ℝ) (254399687943/500000000000 : ℝ) (254399687947/500000000000 : ℝ) (248439677/488281250 : ℝ) (63600557313/125000000000 : ℝ) (508804458471/1000000000000 : ℝ) (508804458479/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (9/64 : ℝ))) 4 (248439677/488281250 : ℝ) (63600557313/125000000000 : ℝ) (508804458471/1000000000000 : ℝ) (508804458479/1000000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (9/64 : ℝ))) 5 (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (9/64 : ℝ))) 6 (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (9/64 : ℝ))) 7 (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (9/64 : ℝ)) hmem 8 (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (9/64 : ℝ))) hcmem 8 (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (9/64 : ℝ)) (495634295673/500000000000 : ℝ) (991268591349/1000000000000 : ℝ) (508804458483/1000000000000 : ℝ) (127201114623/250000000000 : ℝ) (403134015047/500000000000 : ℝ) (25195875941/31250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1688_exp_lower
  have heNumeric : (2055269926429/1000000000000 : ℝ)/4 ≤ Real.exp (-665887170737/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055269926429/1000000000000 : ℝ)/4 ≤ Real.exp ((575/4096 : ℝ)-(25195875941/31250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (575/4096 : ℝ) (9/64 : ℝ) (25195875941/31250000000 : ℝ) (2055269926429/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1689; no trusted numerical premise.
theorem cover8_leaf1689_exp_radius : (997801340278722131/1000000000000000000 : ℝ) ≤ Real.exp ((-577/32768 : ℝ)/8) ∧ Real.exp ((-577/32768 : ℝ)/8) ≤ (249450335069680533/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-577/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1689_exp_lower : (184027171391118779/200000000000000000 : ℝ) ≤ Real.exp ((-665871593899/1000000000000 : ℝ)/8) ∧ Real.exp ((-665871593899/1000000000000 : ℝ)/8) ≤ (115016982119449237/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665871593899/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1689_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (411060388257/200000000000 : ℝ) ≤ 4*Real.exp (9/64 : ℝ)*Real.exp (-mu (radius 8 (577/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (411060388257/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (577/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1689_exp_radius
  have hrNumeric : (982545483591/1000000000000 : ℝ) ≤ Real.exp (-577/32768 : ℝ) ∧ Real.exp (-577/32768 : ℝ) ≤ (122818185449/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982545483591/1000000000000 : ℝ) ≤ (radius 8 (577/4096 : ℝ)) ∧ (radius 8 (577/4096 : ℝ)) ≤ (122818185449/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (577/4096 : ℝ)) (982545483591/1000000000000 : ℝ) (122818185449/125000000000 : ℝ) (186022505823/1000000000000 : ℝ) (18602250583/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (577/4096 : ℝ)) (982545483591/1000000000000 : ℝ) (122818185449/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (577/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982545483591/1000000000000 : ℝ) (122818185449/125000000000 : ℝ) (198254548359/200000000000 : ℝ) (247818185449/250000000000 : ℝ) (991234323251/1000000000000 : ℝ) (247808580813/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (577/4096 : ℝ)) 1 (198254548359/200000000000 : ℝ) (247818185449/250000000000 : ℝ) (991234323251/1000000000000 : ℝ) (247808580813/250000000000 : ℝ) (991253532523/1000000000000 : ℝ) (247813383131/250000000000 : ℝ) (61953345771/62500000000 : ℝ) (495626766169/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (577/4096 : ℝ)) 2 (991253532523/1000000000000 : ℝ) (247813383131/250000000000 : ℝ) (61953345771/62500000000 : ℝ) (495626766169/500000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (577/4096 : ℝ)) 3 (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (577/4096 : ℝ)) 4 (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (577/4096 : ℝ)) 5 (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (577/4096 : ℝ)) 6 (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (577/4096 : ℝ)) 7 (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (577/4096 : ℝ))) (186022505823/1000000000000 : ℝ) (18602250583/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (577/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (186022505823/1000000000000 : ℝ) (18602250583/100000000000 : ℝ) (593011252911/1000000000000 : ℝ) (118602250583/200000000000 : ℝ) (431303264331/1000000000000 : ℝ) (21565163217/50000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (577/4096 : ℝ))) 1 (593011252911/1000000000000 : ℝ) (118602250583/200000000000 : ℝ) (431303264331/1000000000000 : ℝ) (21565163217/50000000000 : ℝ) (512157258621/1000000000000 : ℝ) (128039314657/250000000000 : ℝ) (25286740061/50000000000 : ℝ) (126433700307/250000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (577/4096 : ℝ))) 2 (512157258621/1000000000000 : ℝ) (128039314657/250000000000 : ℝ) (25286740061/50000000000 : ℝ) (126433700307/250000000000 : ℝ) (3180912687/6250000000 : ℝ) (63618253741/125000000000 : ℝ) (508935899089/1000000000000 : ℝ) (254467949549/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (577/4096 : ℝ))) 3 (3180912687/6250000000 : ℝ) (63618253741/125000000000 : ℝ) (508935899089/1000000000000 : ℝ) (254467949549/500000000000 : ℝ) (63617620563/125000000000 : ℝ) (508940964513/1000000000000 : ℝ) (508940964479/1000000000000 : ℝ) (63617620561/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (577/4096 : ℝ))) 4 (63617620563/125000000000 : ℝ) (508940964513/1000000000000 : ℝ) (508940964479/1000000000000 : ℝ) (63617620561/125000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (577/4096 : ℝ))) 5 (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (577/4096 : ℝ))) 6 (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (577/4096 : ℝ))) 7 (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (577/4096 : ℝ)) hmem 8 (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (577/4096 : ℝ))) hcmem 8 (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (577/4096 : ℝ)) (991253532429/1000000000000 : ℝ) (991253532431/1000000000000 : ℝ) (508940964491/1000000000000 : ℝ) (508940964501/1000000000000 : ℝ) (20162414847/25000000000 : ℝ) (806496593899/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1689_exp_lower
  have heNumeric : (411060388257/200000000000 : ℝ)/4 ≤ Real.exp (-665871593899/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (411060388257/200000000000 : ℝ)/4 ≤ Real.exp ((9/64 : ℝ)-(806496593899/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (9/64 : ℝ) (577/4096 : ℝ) (806496593899/1000000000000 : ℝ) (411060388257/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1690; no trusted numerical premise.
theorem cover8_leaf1690_exp_radius : (249449383493984421/250000000000000000 : ℝ) ≤ Real.exp ((-289/16384 : ℝ)/8) ∧ Real.exp ((-289/16384 : ℝ)/8) ≤ (199559506795187537/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-289/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1690_exp_lower : (920137679210896851/1000000000000000000 : ℝ) ≤ Real.exp ((-166463937639/250000000000 : ℝ)/8) ∧ Real.exp ((-166463937639/250000000000 : ℝ)/8) ≤ (230034419802724213/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-166463937639/250000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1690_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513833626099/250000000000 : ℝ) ≤ 4*Real.exp (577/4096 : ℝ)*Real.exp (-mu (radius 8 (289/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (513833626099/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (289/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1690_exp_radius
  have hrNumeric : (49125774957/50000000000 : ℝ) ≤ Real.exp (-289/16384 : ℝ) ∧ Real.exp (-289/16384 : ℝ) ≤ (982515499141/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (49125774957/50000000000 : ℝ) ≤ (radius 8 (289/2048 : ℝ)) ∧ (radius 8 (289/2048 : ℝ)) ≤ (982515499141/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (289/2048 : ℝ)) (49125774957/50000000000 : ℝ) (982515499141/1000000000000 : ℝ) (93090404913/500000000000 : ℝ) (23272601229/125000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (289/2048 : ℝ)) (49125774957/50000000000 : ℝ) (982515499141/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (289/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (49125774957/50000000000 : ℝ) (982515499141/1000000000000 : ℝ) (99125774957/100000000000 : ℝ) (991257749571/1000000000000 : ℝ) (991219198331/1000000000000 : ℝ) (247804799583/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (289/2048 : ℝ)) 1 (99125774957/100000000000 : ℝ) (991257749571/1000000000000 : ℝ) (991219198331/1000000000000 : ℝ) (247804799583/250000000000 : ℝ) (19824769479/20000000000 : ℝ) (30976202311/31250000000 : ℝ) (991238473763/1000000000000 : ℝ) (198247694753/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (289/2048 : ℝ)) 2 (19824769479/20000000000 : ℝ) (30976202311/31250000000 : ℝ) (991238473763/1000000000000 : ℝ) (198247694753/200000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (289/2048 : ℝ)) 3 (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (289/2048 : ℝ)) 4 (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (289/2048 : ℝ)) 5 (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (289/2048 : ℝ)) 6 (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (289/2048 : ℝ)) 7 (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (289/2048 : ℝ))) (93090404913/500000000000 : ℝ) (23272601229/125000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (289/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (93090404913/500000000000 : ℝ) (23272601229/125000000000 : ℝ) (593090404913/1000000000000 : ℝ) (148272601229/250000000000 : ℝ) (431486743511/1000000000000 : ℝ) (431486743519/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (289/2048 : ℝ))) 1 (593090404913/1000000000000 : ℝ) (148272601229/250000000000 : ℝ) (431486743511/1000000000000 : ℝ) (431486743519/1000000000000 : ℝ) (128072143553/250000000000 : ℝ) (256144287109/500000000000 : ℝ) (505876118653/1000000000000 : ℝ) (25293805933/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (289/2048 : ℝ))) 2 (128072143553/250000000000 : ℝ) (256144287109/500000000000 : ℝ) (505876118653/1000000000000 : ℝ) (25293805933/50000000000 : ℝ) (7954411663/15625000000 : ℝ) (509082346439/1000000000000 : ℝ) (101814449967/200000000000 : ℝ) (509072249843/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (289/2048 : ℝ))) 3 (7954411663/15625000000 : ℝ) (509082346439/1000000000000 : ℝ) (101814449967/200000000000 : ℝ) (509072249843/1000000000000 : ℝ) (509077298133/1000000000000 : ℝ) (509077298141/1000000000000 : ℝ) (127269324527/250000000000 : ℝ) (127269324529/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (289/2048 : ℝ))) 4 (509077298133/1000000000000 : ℝ) (509077298141/1000000000000 : ℝ) (127269324527/250000000000 : ℝ) (127269324529/250000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (289/2048 : ℝ))) 5 (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (289/2048 : ℝ))) 6 (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (289/2048 : ℝ))) 7 (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (289/2048 : ℝ)) hmem 8 (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (289/2048 : ℝ))) hcmem 8 (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (289/2048 : ℝ)) (7744050577/7812500000 : ℝ) (991238473859/1000000000000 : ℝ) (12726932453/25000000000 : ℝ) (509077298129/1000000000000 : ℝ) (201681222791/250000000000 : ℝ) (806724891181/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1690_exp_lower
  have heNumeric : (513833626099/250000000000 : ℝ)/4 ≤ Real.exp (-166463937639/250000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513833626099/250000000000 : ℝ)/4 ≤ Real.exp ((577/4096 : ℝ)-(806724891181/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (577/4096 : ℝ) (289/2048 : ℝ) (806724891181/1000000000000 : ℝ) (513833626099/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1691; no trusted numerical premise.
theorem cover8_leaf1691_exp_radius : (498896863843836551/500000000000000000 : ℝ) ≤ Real.exp ((-579/32768 : ℝ)/8) ∧ Real.exp ((-579/32768 : ℝ)/8) ≤ (997793727687673103/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-579/32768 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1691_exp_lower : (460069766014511099/500000000000000000 : ℝ) ≤ Real.exp ((-665839641521/1000000000000 : ℝ)/8) ∧ Real.exp ((-665839641521/1000000000000 : ℝ)/8) ≤ (920139532029022199/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665839641521/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1691_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055367614119/1000000000000 : ℝ) ≤ 4*Real.exp (289/2048 : ℝ)*Real.exp (-mu (radius 8 (579/4096 : ℝ))) ∧ (20549/10000 : ℝ) < (2055367614119/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (579/4096 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1691_exp_radius
  have hrNumeric : (245621378901/250000000000 : ℝ) ≤ Real.exp (-579/32768 : ℝ) ∧ Real.exp (-579/32768 : ℝ) ≤ (196497103121/200000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245621378901/250000000000 : ℝ) ≤ (radius 8 (579/4096 : ℝ)) ∧ (radius 8 (579/4096 : ℝ)) ≤ (196497103121/200000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (579/4096 : ℝ)) (245621378901/250000000000 : ℝ) (196497103121/200000000000 : ℝ) (186338969693/1000000000000 : ℝ) (186338969699/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (579/4096 : ℝ)) (245621378901/250000000000 : ℝ) (196497103121/200000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (579/4096 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245621378901/250000000000 : ℝ) (196497103121/200000000000 : ℝ) (495621378901/500000000000 : ℝ) (991242757803/1000000000000 : ℝ) (991204073641/1000000000000 : ℝ) (991204073643/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (579/4096 : ℝ)) 1 (495621378901/500000000000 : ℝ) (991242757803/1000000000000 : ℝ) (991204073641/1000000000000 : ℝ) (991204073643/1000000000000 : ℝ) (991223415721/1000000000000 : ℝ) (991223415723/1000000000000 : ℝ) (247805853883/250000000000 : ℝ) (198244683107/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (579/4096 : ℝ)) 2 (991223415721/1000000000000 : ℝ) (991223415723/1000000000000 : ℝ) (247805853883/250000000000 : ℝ) (198244683107/200000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (579/4096 : ℝ)) 3 (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (579/4096 : ℝ)) 4 (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (579/4096 : ℝ)) 5 (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (579/4096 : ℝ)) 6 (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (579/4096 : ℝ)) 7 (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (579/4096 : ℝ))) (186338969693/1000000000000 : ℝ) (186338969699/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (579/4096 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (186338969693/1000000000000 : ℝ) (186338969699/1000000000000 : ℝ) (296584742423/500000000000 : ℝ) (11863389697/20000000000 : ℝ) (53958747219/125000000000 : ℝ) (2697937361/6250000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (579/4096 : ℝ))) 1 (296584742423/500000000000 : ℝ) (11863389697/20000000000 : ℝ) (53958747219/125000000000 : ℝ) (2697937361/6250000000 : ℝ) (512419731299/1000000000000 : ℝ) (102483946261/200000000000 : ℝ) (63252156377/125000000000 : ℝ) (31626078189/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (579/4096 : ℝ))) 2 (512419731299/1000000000000 : ℝ) (102483946261/200000000000 : ℝ) (63252156377/125000000000 : ℝ) (31626078189/62500000000 : ℝ) (509218491157/1000000000000 : ℝ) (101843698233/200000000000 : ℝ) (3182552679/6250000000 : ℝ) (63651053581/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (579/4096 : ℝ))) 3 (509218491157/1000000000000 : ℝ) (101843698233/200000000000 : ℝ) (3182552679/6250000000 : ℝ) (63651053581/125000000000 : ℝ) (254606729949/500000000000 : ℝ) (509213459907/1000000000000 : ℝ) (509213459873/1000000000000 : ℝ) (254606729941/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (579/4096 : ℝ))) 4 (254606729949/500000000000 : ℝ) (509213459907/1000000000000 : ℝ) (509213459873/1000000000000 : ℝ) (254606729941/500000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (579/4096 : ℝ))) 5 (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (579/4096 : ℝ))) 6 (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (579/4096 : ℝ))) 7 (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (579/4096 : ℝ)) hmem 8 (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (579/4096 : ℝ))) hcmem 8 (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (579/4096 : ℝ)) (495611707813/500000000000 : ℝ) (991223415629/1000000000000 : ℝ) (101842691977/200000000000 : ℝ) (101842691979/200000000000 : ℝ) (806952922751/1000000000000 : ℝ) (806952922771/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1691_exp_lower
  have heNumeric : (2055367614119/1000000000000 : ℝ)/4 ≤ Real.exp (-665839641521/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055367614119/1000000000000 : ℝ)/4 ≤ Real.exp ((289/2048 : ℝ)-(806952922771/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (289/2048 : ℝ) (579/4096 : ℝ) (806952922771/1000000000000 : ℝ) (2055367614119/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1692; no trusted numerical premise.
theorem cover8_leaf1692_exp_radius : (99778992141392833/100000000000000000 : ℝ) ≤ Real.exp ((-145/8192 : ℝ)/8) ∧ Real.exp ((-145/8192 : ℝ)/8) ≤ (997789921413928331/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-145/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1692_exp_lower : (46007070765924273/50000000000000000 : ℝ) ≤ Real.exp ((-665823267591/1000000000000 : ℝ)/8) ∧ Real.exp ((-665823267591/1000000000000 : ℝ)/8) ≤ (920141415318485461/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665823267591/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1692_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (51385031721/25000000000 : ℝ) ≤ 4*Real.exp (579/4096 : ℝ)*Real.exp (-mu (radius 8 (145/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (51385031721/25000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (145/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1692_exp_radius
  have hrNumeric : (982455532983/1000000000000 : ℝ) ≤ Real.exp (-145/8192 : ℝ) ∧ Real.exp (-145/8192 : ℝ) ≤ (122806941623/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982455532983/1000000000000 : ℝ) ≤ (radius 8 (145/1024 : ℝ)) ∧ (radius 8 (145/1024 : ℝ)) ≤ (122806941623/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (145/1024 : ℝ)) (982455532983/1000000000000 : ℝ) (122806941623/125000000000 : ℝ) (18649698579/100000000000 : ℝ) (186496985797/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (145/1024 : ℝ)) (982455532983/1000000000000 : ℝ) (122806941623/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (145/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982455532983/1000000000000 : ℝ) (122806941623/125000000000 : ℝ) (991227766491/1000000000000 : ℝ) (247806941623/250000000000 : ℝ) (991188949183/1000000000000 : ℝ) (15487327331/15625000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (145/1024 : ℝ)) 1 (991227766491/1000000000000 : ℝ) (247806941623/250000000000 : ℝ) (991188949183/1000000000000 : ℝ) (15487327331/15625000000 : ℝ) (991208357837/1000000000000 : ℝ) (495604178919/500000000000 : ℝ) (495604178823/500000000000 : ℝ) (61950522353/62500000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (145/1024 : ℝ)) 2 (991208357837/1000000000000 : ℝ) (495604178919/500000000000 : ℝ) (495604178823/500000000000 : ℝ) (61950522353/62500000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (145/1024 : ℝ)) 3 (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (145/1024 : ℝ)) 4 (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (145/1024 : ℝ)) 5 (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (145/1024 : ℝ)) 6 (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (145/1024 : ℝ)) 7 (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (145/1024 : ℝ))) (18649698579/100000000000 : ℝ) (186496985797/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (145/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (18649698579/100000000000 : ℝ) (186496985797/1000000000000 : ℝ) (118649698579/200000000000 : ℝ) (593248492899/1000000000000 : ℝ) (431852967791/1000000000000 : ℝ) (2159264839/5000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (145/1024 : ℝ))) 1 (118649698579/200000000000 : ℝ) (593248492899/1000000000000 : ℝ) (431852967791/1000000000000 : ℝ) (2159264839/5000000000 : ℝ) (512550730343/1000000000000 : ℝ) (10251014607/20000000000 : ℝ) (3163488743/6250000000 : ℝ) (63269774861/125000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (145/1024 : ℝ))) 2 (512550730343/1000000000000 : ℝ) (10251014607/20000000000 : ℝ) (3163488743/6250000000 : ℝ) (63269774861/125000000000 : ℝ) (509354464611/1000000000000 : ℝ) (509354464619/1000000000000 : ℝ) (25467221801/50000000000 : ℝ) (509344436029/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (145/1024 : ℝ))) 3 (509354464611/1000000000000 : ℝ) (509354464619/1000000000000 : ℝ) (25467221801/50000000000 : ℝ) (509344436029/1000000000000 : ℝ) (101869890063/200000000000 : ℝ) (127337362581/250000000000 : ℝ) (50934945029/100000000000 : ℝ) (5093494503/10000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (145/1024 : ℝ))) 4 (101869890063/200000000000 : ℝ) (127337362581/250000000000 : ℝ) (50934945029/100000000000 : ℝ) (5093494503/10000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (145/1024 : ℝ))) 5 (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (145/1024 : ℝ))) 6 (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (145/1024 : ℝ))) 7 (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (145/1024 : ℝ)) hmem 8 (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (145/1024 : ℝ))) hcmem 8 (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (145/1024 : ℝ)) (991208357741/1000000000000 : ℝ) (991208357743/1000000000000 : ℝ) (254674725151/500000000000 : ℝ) (63668681289/125000000000 : ℝ) (807180689447/1000000000000 : ℝ) (403590344733/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1692_exp_lower
  have heNumeric : (51385031721/25000000000 : ℝ)/4 ≤ Real.exp (-665823267591/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (51385031721/25000000000 : ℝ)/4 ≤ Real.exp ((579/4096 : ℝ)-(403590344733/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (579/4096 : ℝ) (145/1024 : ℝ) (403590344733/500000000000 : ℝ) (51385031721/25000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1693; no trusted numerical premise.
theorem cover8_leaf1693_exp_radius : (997782308909997993/1000000000000000000 : ℝ) ≤ Real.exp ((-291/16384 : ℝ)/8) ∧ Real.exp ((-291/16384 : ℝ)/8) ≤ (498891154454998997/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-291/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1693_exp_lower : (920117192766992197/1000000000000000000 : ℝ) ≤ Real.exp ((-333016934437/500000000000 : ℝ)/8) ∧ Real.exp ((-333016934437/500000000000 : ℝ)/8) ≤ (460058596383496099/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-333016934437/500000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1693_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027484222137/500000000000 : ℝ) ≤ 4*Real.exp (145/1024 : ℝ)*Real.exp (-mu (radius 8 (291/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (1027484222137/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (291/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1693_exp_radius
  have hrNumeric : (491197785243/500000000000 : ℝ) ≤ Real.exp (-291/16384 : ℝ) ∧ Real.exp (-291/16384 : ℝ) ≤ (982395570487/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491197785243/500000000000 : ℝ) ≤ (radius 8 (291/2048 : ℝ)) ∧ (radius 8 (291/2048 : ℝ)) ≤ (982395570487/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (291/2048 : ℝ)) (491197785243/500000000000 : ℝ) (982395570487/1000000000000 : ℝ) (186812588139/1000000000000 : ℝ) (93406294073/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (291/2048 : ℝ)) (491197785243/500000000000 : ℝ) (982395570487/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (291/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491197785243/500000000000 : ℝ) (982395570487/1000000000000 : ℝ) (991197785243/1000000000000 : ℝ) (247799446311/250000000000 : ℝ) (495579350479/500000000000 : ℝ) (6194741881/6250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (291/2048 : ℝ)) 1 (991197785243/1000000000000 : ℝ) (247799446311/250000000000 : ℝ) (495579350479/500000000000 : ℝ) (6194741881/6250000000 : ℝ) (9911782431/10000000000 : ℝ) (495589121551/500000000000 : ℝ) (991178242907/1000000000000 : ℝ) (99117824291/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (291/2048 : ℝ)) 2 (9911782431/10000000000 : ℝ) (495589121551/500000000000 : ℝ) (991178242907/1000000000000 : ℝ) (99117824291/100000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (291/2048 : ℝ)) 3 (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (291/2048 : ℝ)) 4 (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (291/2048 : ℝ)) 5 (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (291/2048 : ℝ)) 6 (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (291/2048 : ℝ)) 7 (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (291/2048 : ℝ))) (186812588139/1000000000000 : ℝ) (93406294073/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (291/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (186812588139/1000000000000 : ℝ) (93406294073/500000000000 : ℝ) (593406294069/1000000000000 : ℝ) (593406294073/1000000000000 : ℝ) (216109109097/500000000000 : ℝ) (432218218203/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (291/2048 : ℝ))) 1 (593406294069/1000000000000 : ℝ) (593406294073/1000000000000 : ℝ) (216109109097/500000000000 : ℝ) (432218218203/1000000000000 : ℝ) (512812256131/1000000000000 : ℝ) (256406128069/500000000000 : ℝ) (63304942921/125000000000 : ℝ) (31652471461/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (291/2048 : ℝ))) 2 (512812256131/1000000000000 : ℝ) (256406128069/500000000000 : ℝ) (63304942921/125000000000 : ℝ) (31652471461/62500000000 : ℝ) (509625899749/1000000000000 : ℝ) (509625899757/1000000000000 : ℝ) (254807969277/500000000000 : ℝ) (254807969281/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (291/2048 : ℝ))) 3 (509625899749/1000000000000 : ℝ) (509625899757/1000000000000 : ℝ) (254807969277/500000000000 : ℝ) (254807969281/500000000000 : ℝ) (509620919151/1000000000000 : ℝ) (12740522979/25000000000 : ℝ) (509620919127/1000000000000 : ℝ) (15925653723/31250000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (291/2048 : ℝ))) 4 (509620919151/1000000000000 : ℝ) (12740522979/25000000000 : ℝ) (509620919127/1000000000000 : ℝ) (15925653723/31250000000 : ℝ) (509620919139/1000000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (291/2048 : ℝ))) 5 (509620919139/1000000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (291/2048 : ℝ))) 6 (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (291/2048 : ℝ))) 7 (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (291/2048 : ℝ)) hmem 8 (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (291/2048 : ℝ))) hcmem 8 (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (291/2048 : ℝ)) (991178243003/1000000000000 : ℝ) (495589121503/500000000000 : ℝ) (254810459569/500000000000 : ℝ) (127405229787/250000000000 : ℝ) (403817715677/500000000000 : ℝ) (403817715687/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1693_exp_lower
  have heNumeric : (1027484222137/500000000000 : ℝ)/4 ≤ Real.exp (-333016934437/500000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027484222137/500000000000 : ℝ)/4 ≤ Real.exp ((145/1024 : ℝ)-(403817715687/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (145/1024 : ℝ) (291/2048 : ℝ) (403817715687/500000000000 : ℝ) (1027484222137/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1694; no trusted numerical premise.
theorem cover8_leaf1694_exp_radius : (99777469646414623/100000000000000000 : ℝ) ≤ Real.exp ((-73/4096 : ℝ)/8) ∧ Real.exp ((-73/4096 : ℝ)/8) ≤ (997774696464146231/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-73/4096 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1694_exp_lower : (7188446648900551/7812500000000000 : ℝ) ≤ Real.exp ((-665999279509/1000000000000 : ℝ)/8) ∧ Real.exp ((-665999279509/1000000000000 : ℝ)/8) ≤ (920121171059270529/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665999279509/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1694_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513759881389/250000000000 : ℝ) ≤ 4*Real.exp (291/2048 : ℝ)*Real.exp (-mu (radius 8 (73/512 : ℝ))) ∧ (20549/10000 : ℝ) < (513759881389/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (73/512 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1694_exp_radius
  have hrNumeric : (982335611649/1000000000000 : ℝ) ≤ Real.exp (-73/4096 : ℝ) ∧ Real.exp (-73/4096 : ℝ) ≤ (19646712233/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982335611649/1000000000000 : ℝ) ≤ (radius 8 (73/512 : ℝ)) ∧ (radius 8 (73/512 : ℝ)) ≤ (19646712233/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (73/512 : ℝ)) (982335611649/1000000000000 : ℝ) (19646712233/20000000000 : ℝ) (187127619779/1000000000000 : ℝ) (37425523957/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (73/512 : ℝ)) (982335611649/1000000000000 : ℝ) (19646712233/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (73/512 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982335611649/1000000000000 : ℝ) (19646712233/20000000000 : ℝ) (7743498483/7812500000 : ℝ) (39646712233/40000000000 : ℝ) (991128453657/1000000000000 : ℝ) (495564226829/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (73/512 : ℝ)) 1 (7743498483/7812500000 : ℝ) (39646712233/40000000000 : ℝ) (991128453657/1000000000000 : ℝ) (495564226829/500000000000 : ℝ) (49557406487/50000000000 : ℝ) (495574064871/500000000000 : ℝ) (198229625909/200000000000 : ℝ) (991148129547/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (73/512 : ℝ)) 2 (49557406487/50000000000 : ℝ) (495574064871/500000000000 : ℝ) (198229625909/200000000000 : ℝ) (991148129547/1000000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (73/512 : ℝ)) 3 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (73/512 : ℝ)) 4 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (73/512 : ℝ)) 5 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (73/512 : ℝ)) 6 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (73/512 : ℝ)) 7 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (73/512 : ℝ))) (187127619779/1000000000000 : ℝ) (37425523957/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (73/512 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (187127619779/1000000000000 : ℝ) (37425523957/200000000000 : ℝ) (593563809889/1000000000000 : ℝ) (593563809893/1000000000000 : ℝ) (216291250273/500000000000 : ℝ) (216291250277/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (73/512 : ℝ))) 1 (593563809889/1000000000000 : ℝ) (593563809893/1000000000000 : ℝ) (216291250273/500000000000 : ℝ) (216291250277/500000000000 : ℝ) (513073155217/1000000000000 : ℝ) (64134144403/125000000000 : ℝ) (50672015661/100000000000 : ℝ) (506720156617/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (73/512 : ℝ))) 2 (513073155217/1000000000000 : ℝ) (64134144403/125000000000 : ℝ) (50672015661/100000000000 : ℝ) (506720156617/1000000000000 : ℝ) (509896655913/1000000000000 : ℝ) (509896655921/1000000000000 : ℝ) (50988676151/100000000000 : ℝ) (254943380759/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (73/512 : ℝ))) 3 (509896655913/1000000000000 : ℝ) (509896655921/1000000000000 : ℝ) (50988676151/100000000000 : ℝ) (254943380759/500000000000 : ℝ) (509891708711/1000000000000 : ℝ) (6373646359/12500000000 : ℝ) (509891708687/1000000000000 : ℝ) (63736463587/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (73/512 : ℝ))) 4 (509891708711/1000000000000 : ℝ) (6373646359/12500000000 : ℝ) (509891708687/1000000000000 : ℝ) (63736463587/125000000000 : ℝ) (509891708699/1000000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (73/512 : ℝ))) 5 (509891708699/1000000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (73/512 : ℝ))) 6 (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (73/512 : ℝ))) 7 (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (73/512 : ℝ)) hmem 8 (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (73/512 : ℝ))) hcmem 8 (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (73/512 : ℝ)) (495574064821/500000000000 : ℝ) (198229625929/200000000000 : ℝ) (254945854349/500000000000 : ℝ) (127472927177/250000000000 : ℝ) (20202228081/25000000000 : ℝ) (808089123259/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1694_exp_lower
  have heNumeric : (513759881389/250000000000 : ℝ)/4 ≤ Real.exp (-665999279509/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513759881389/250000000000 : ℝ)/4 ≤ Real.exp ((291/2048 : ℝ)-(808089123259/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (291/2048 : ℝ) (73/512 : ℝ) (808089123259/1000000000000 : ℝ) (513759881389/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1695; no trusted numerical premise.
theorem cover8_leaf1695_exp_radius : (997767084076372599/1000000000000000000 : ℝ) ≤ Real.exp ((-293/16384 : ℝ)/8) ∧ Real.exp ((-293/16384 : ℝ)/8) ≤ (4988835420381863/5000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-293/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1695_exp_lower : (920125269413345227/1000000000000000000 : ℝ) ≤ Real.exp ((-33298182321/50000000000 : ℝ)/8) ∧ Real.exp ((-33298182321/50000000000 : ℝ)/8) ≤ (230031317353336307/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33298182321/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1695_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055112754267/1000000000000 : ℝ) ≤ 4*Real.exp (73/512 : ℝ)*Real.exp (-mu (radius 8 (293/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (2055112754267/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (293/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1695_exp_radius
  have hrNumeric : (982275656471/1000000000000 : ℝ) ≤ Real.exp (-293/16384 : ℝ) ∧ Real.exp (-293/16384 : ℝ) ≤ (122784457059/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982275656471/1000000000000 : ℝ) ≤ (radius 8 (293/2048 : ℝ)) ∧ (radius 8 (293/2048 : ℝ)) ≤ (122784457059/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (293/2048 : ℝ)) (982275656471/1000000000000 : ℝ) (122784457059/125000000000 : ℝ) (37488416719/200000000000 : ℝ) (187442083601/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (293/2048 : ℝ)) (982275656471/1000000000000 : ℝ) (122784457059/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (293/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982275656471/1000000000000 : ℝ) (122784457059/125000000000 : ℝ) (198227565647/200000000000 : ℝ) (247784457059/250000000000 : ℝ) (495549103639/500000000000 : ℝ) (12388727591/12500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (293/2048 : ℝ)) 1 (198227565647/200000000000 : ℝ) (247784457059/250000000000 : ℝ) (495549103639/500000000000 : ℝ) (12388727591/12500000000 : ℝ) (247779504439/250000000000 : ℝ) (495559008879/500000000000 : ℝ) (495559008779/500000000000 : ℝ) (991118017561/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (293/2048 : ℝ)) 2 (247779504439/250000000000 : ℝ) (495559008879/500000000000 : ℝ) (495559008779/500000000000 : ℝ) (991118017561/1000000000000 : ℝ) (991118017657/1000000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (293/2048 : ℝ)) 3 (991118017657/1000000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (293/2048 : ℝ)) 4 (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (293/2048 : ℝ)) 5 (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (293/2048 : ℝ)) 6 (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (293/2048 : ℝ)) 7 (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (293/2048 : ℝ))) (37488416719/200000000000 : ℝ) (187442083601/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (293/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (37488416719/200000000000 : ℝ) (187442083601/1000000000000 : ℝ) (593721041797/1000000000000 : ℝ) (593721041801/1000000000000 : ℝ) (432945820623/1000000000000 : ℝ) (432945820631/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (293/2048 : ℝ))) 1 (593721041797/1000000000000 : ℝ) (593721041801/1000000000000 : ℝ) (432945820623/1000000000000 : ℝ) (432945820631/1000000000000 : ℝ) (51333343121/100000000000 : ℝ) (32083339451/62500000000 : ℝ) (507000043059/1000000000000 : ℝ) (253500021533/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (293/2048 : ℝ))) 2 (51333343121/100000000000 : ℝ) (32083339451/62500000000 : ℝ) (507000043059/1000000000000 : ℝ) (253500021533/500000000000 : ℝ) (255083368567/500000000000 : ℝ) (510166737141/1000000000000 : ℝ) (3985600851/7812500000 : ℝ) (102031381787/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (293/2048 : ℝ))) 3 (255083368567/500000000000 : ℝ) (510166737141/1000000000000 : ℝ) (3985600851/7812500000 : ℝ) (102031381787/200000000000 : ℝ) (510161823031/1000000000000 : ℝ) (255080911519/500000000000 : ℝ) (510161823007/1000000000000 : ℝ) (102032364603/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (293/2048 : ℝ))) 4 (510161823031/1000000000000 : ℝ) (255080911519/500000000000 : ℝ) (510161823007/1000000000000 : ℝ) (102032364603/200000000000 : ℝ) (510161823019/1000000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (293/2048 : ℝ))) 5 (510161823019/1000000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (293/2048 : ℝ))) 6 (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (293/2048 : ℝ))) 7 (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (293/2048 : ℝ)) hmem 8 (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (293/2048 : ℝ))) hcmem 8 (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (293/2048 : ℝ)) (123889752207/125000000000 : ℝ) (49555900883/50000000000 : ℝ) (255080911509/500000000000 : ℝ) (510161823027/1000000000000 : ℝ) (404270885701/500000000000 : ℝ) (40427088571/50000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1695_exp_lower
  have heNumeric : (2055112754267/1000000000000 : ℝ)/4 ≤ Real.exp (-33298182321/50000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055112754267/1000000000000 : ℝ)/4 ≤ Real.exp ((73/512 : ℝ)-(40427088571/50000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (73/512 : ℝ) (293/2048 : ℝ) (40427088571/50000000000 : ℝ) (2055112754267/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1696; no trusted numerical premise.
theorem cover8_leaf1696_exp_radius : (199551894349335331/200000000000000000 : ℝ) ≤ Real.exp ((-147/8192 : ℝ)/8) ∧ Real.exp ((-147/8192 : ℝ)/8) ≤ (62359966984167291/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-147/8192 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1696_exp_lower : (230032371778797437/250000000000000000 : ℝ) ≤ Real.exp ((-665926975829/1000000000000 : ℝ)/8) ∧ Real.exp ((-665926975829/1000000000000 : ℝ)/8) ≤ (920129487115189749/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665926975829/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1696_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2055188117849/1000000000000 : ℝ) ≤ 4*Real.exp (293/2048 : ℝ)*Real.exp (-mu (radius 8 (147/1024 : ℝ))) ∧ (20549/10000 : ℝ) < (2055188117849/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (147/1024 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1696_exp_radius
  have hrNumeric : (982215704953/1000000000000 : ℝ) ≤ Real.exp (-147/8192 : ℝ) ∧ Real.exp (-147/8192 : ℝ) ≤ (491107852477/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982215704953/1000000000000 : ℝ) ≤ (radius 8 (147/1024 : ℝ)) ∧ (radius 8 (147/1024 : ℝ)) ≤ (491107852477/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (147/1024 : ℝ)) (982215704953/1000000000000 : ℝ) (491107852477/500000000000 : ℝ) (187755982439/1000000000000 : ℝ) (37551196489/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (147/1024 : ℝ)) (982215704953/1000000000000 : ℝ) (491107852477/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (147/1024 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982215704953/1000000000000 : ℝ) (491107852477/500000000000 : ℝ) (247776963119/250000000000 : ℝ) (991107852477/1000000000000 : ℝ) (991067961823/1000000000000 : ℝ) (39642718473/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (147/1024 : ℝ)) 1 (247776963119/250000000000 : ℝ) (991107852477/1000000000000 : ℝ) (991067961823/1000000000000 : ℝ) (39642718473/40000000000 : ℝ) (991087907149/1000000000000 : ℝ) (991087907151/1000000000000 : ℝ) (247771976737/250000000000 : ℝ) (991087906951/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (147/1024 : ℝ)) 2 (991087907149/1000000000000 : ℝ) (991087907151/1000000000000 : ℝ) (247771976737/250000000000 : ℝ) (991087906951/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (147/1024 : ℝ)) 3 (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (147/1024 : ℝ)) 4 (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (147/1024 : ℝ)) 5 (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (147/1024 : ℝ)) 6 (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (147/1024 : ℝ)) 7 (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (147/1024 : ℝ))) (187755982439/1000000000000 : ℝ) (37551196489/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (147/1024 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (187755982439/1000000000000 : ℝ) (37551196489/200000000000 : ℝ) (593877991219/1000000000000 : ℝ) (593877991223/1000000000000 : ℝ) (86661636827/200000000000 : ℝ) (433308184143/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (147/1024 : ℝ))) 1 (593877991219/1000000000000 : ℝ) (593877991223/1000000000000 : ℝ) (86661636827/200000000000 : ℝ) (433308184143/1000000000000 : ℝ) (513593087677/1000000000000 : ℝ) (513593087683/1000000000000 : ℝ) (126819801779/250000000000 : ℝ) (507279207123/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (147/1024 : ℝ))) 2 (513593087677/1000000000000 : ℝ) (513593087683/1000000000000 : ℝ) (126819801779/250000000000 : ℝ) (507279207123/1000000000000 : ℝ) (127609036849/250000000000 : ℝ) (510436147403/1000000000000 : ℝ) (510426384797/1000000000000 : ℝ) (127606596201/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (147/1024 : ℝ))) 3 (127609036849/250000000000 : ℝ) (510436147403/1000000000000 : ℝ) (510426384797/1000000000000 : ℝ) (127606596201/250000000000 : ℝ) (31901954131/62500000000 : ℝ) (63803908263/125000000000 : ℝ) (510431266073/1000000000000 : ℝ) (510431266081/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (147/1024 : ℝ))) 4 (31901954131/62500000000 : ℝ) (63803908263/125000000000 : ℝ) (510431266073/1000000000000 : ℝ) (510431266081/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (147/1024 : ℝ))) 5 (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (147/1024 : ℝ))) 6 (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (147/1024 : ℝ))) 7 (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (147/1024 : ℝ)) hmem 8 (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (147/1024 : ℝ))) hcmem 8 (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (147/1024 : ℝ)) (123885988381/125000000000 : ℝ) (991087907051/1000000000000 : ℝ) (127607816521/250000000000 : ℝ) (510431266093/1000000000000 : ℝ) (404496691031/500000000000 : ℝ) (808993382079/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1696_exp_lower
  have heNumeric : (2055188117849/1000000000000 : ℝ)/4 ≤ Real.exp (-665926975829/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2055188117849/1000000000000 : ℝ)/4 ≤ Real.exp ((293/2048 : ℝ)-(808993382079/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (293/2048 : ℝ) (147/1024 : ℝ) (808993382079/1000000000000 : ℝ) (2055188117849/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1697; no trusted numerical premise.
theorem cover8_leaf1697_exp_radius : (997751859475057957/1000000000000000000 : ℝ) ≤ Real.exp ((-295/16384 : ℝ)/8) ∧ Real.exp ((-295/16384 : ℝ)/8) ≤ (498875929737528979/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-295/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1697_exp_lower : (460066911727130777/500000000000000000 : ℝ) ≤ Real.exp ((-83236159241/125000000000 : ℝ)/8) ∧ Real.exp ((-83236159241/125000000000 : ℝ)/8) ≤ (184026764690852311/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-83236159241/125000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1697_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (64227050119/31250000000 : ℝ) ≤ 4*Real.exp (147/1024 : ℝ)*Real.exp (-mu (radius 8 (295/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (64227050119/31250000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (295/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1697_exp_radius
  have hrNumeric : (982155757093/1000000000000 : ℝ) ≤ Real.exp (-295/16384 : ℝ) ∧ Real.exp (-295/16384 : ℝ) ≤ (491077878547/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (982155757093/1000000000000 : ℝ) ≤ (radius 8 (295/2048 : ℝ)) ∧ (radius 8 (295/2048 : ℝ)) ≤ (491077878547/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (295/2048 : ℝ)) (982155757093/1000000000000 : ℝ) (491077878547/500000000000 : ℝ) (94034659577/500000000000 : ℝ) (4701732979/25000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (295/2048 : ℝ)) (982155757093/1000000000000 : ℝ) (491077878547/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (295/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (982155757093/1000000000000 : ℝ) (491077878547/500000000000 : ℝ) (495538939273/500000000000 : ℝ) (991077878547/1000000000000 : ℝ) (99103771729/100000000000 : ℝ) (247759429323/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (295/2048 : ℝ)) 1 (495538939273/500000000000 : ℝ) (991077878547/1000000000000 : ℝ) (99103771729/100000000000 : ℝ) (247759429323/250000000000 : ℝ) (495528898959/500000000000 : ℝ) (6194111237/6250000000 : ℝ) (495528898857/500000000000 : ℝ) (991057797717/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (295/2048 : ℝ)) 2 (495528898959/500000000000 : ℝ) (6194111237/6250000000 : ℝ) (495528898857/500000000000 : ℝ) (991057797717/1000000000000 : ℝ) (123882224727/125000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (295/2048 : ℝ)) 3 (123882224727/125000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (295/2048 : ℝ)) 4 (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (295/2048 : ℝ)) 5 (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (295/2048 : ℝ)) 6 (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (295/2048 : ℝ)) 7 (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (295/2048 : ℝ))) (94034659577/500000000000 : ℝ) (4701732979/25000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (295/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (94034659577/500000000000 : ℝ) (4701732979/25000000000 : ℝ) (594034659577/1000000000000 : ℝ) (29701732979/50000000000 : ℝ) (10841739919/25000000000 : ℝ) (433669596767/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (295/2048 : ℝ))) 1 (594034659577/1000000000000 : ℝ) (29701732979/50000000000 : ℝ) (10841739919/25000000000 : ℝ) (433669596767/1000000000000 : ℝ) (64231516021/125000000000 : ℝ) (256926064087/500000000000 : ℝ) (253778826579/500000000000 : ℝ) (101511530633/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (295/2048 : ℝ))) 2 (64231516021/125000000000 : ℝ) (256926064087/500000000000 : ℝ) (253778826579/500000000000 : ℝ) (101511530633/200000000000 : ℝ) (510704890663/1000000000000 : ℝ) (51070489067/100000000000 : ℝ) (997451549/1953125000 : ℝ) (102139038619/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (295/2048 : ℝ))) 3 (510704890663/1000000000000 : ℝ) (51070489067/100000000000 : ℝ) (997451549/1953125000 : ℝ) (102139038619/200000000000 : ℝ) (817120067/1600000000 : ℝ) (510700041883/1000000000000 : ℝ) (127675010463/250000000000 : ℝ) (25535002093/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (295/2048 : ℝ))) 4 (817120067/1600000000 : ℝ) (510700041883/1000000000000 : ℝ) (127675010463/250000000000 : ℝ) (25535002093/50000000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (295/2048 : ℝ))) 5 (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (295/2048 : ℝ))) 6 (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (295/2048 : ℝ))) 7 (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (295/2048 : ℝ)) hmem 8 (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (295/2048 : ℝ))) hcmem 8 (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (295/2048 : ℝ)) (198211559563/200000000000 : ℝ) (991057797819/1000000000000 : ℝ) (510700041863/1000000000000 : ℝ) (31918752617/62500000000 : ℝ) (809443961409/1000000000000 : ℝ) (202360990357/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1697_exp_lower
  have heNumeric : (64227050119/31250000000 : ℝ)/4 ≤ Real.exp (-83236159241/125000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (64227050119/31250000000 : ℝ)/4 ≤ Real.exp ((147/1024 : ℝ)-(202360990357/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (147/1024 : ℝ) (295/2048 : ℝ) (202360990357/250000000000 : ℝ) (64227050119/31250000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1698; no trusted numerical premise.
theorem cover8_leaf1698_exp_radius : (997744247261516061/1000000000000000000 : ℝ) ≤ Real.exp ((-37/2048 : ℝ)/8) ∧ Real.exp ((-37/2048 : ℝ)/8) ≤ (498872123630758031/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-37/2048 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1698_exp_lower : (920138277730287293/1000000000000000000 : ℝ) ≤ Real.exp ((-33292527341/50000000000 : ℝ)/8) ∧ Real.exp ((-33292527341/50000000000 : ℝ)/8) ≤ (460069138865143647/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-33292527341/50000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1698_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027672599921/500000000000 : ℝ) ≤ 4*Real.exp (295/2048 : ℝ)*Real.exp (-mu (radius 8 (37/256 : ℝ))) ∧ (20549/10000 : ℝ) < (1027672599921/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (37/256 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1698_exp_radius
  have hrNumeric : (245523953223/250000000000 : ℝ) ≤ Real.exp (-37/2048 : ℝ) ∧ Real.exp (-37/2048 : ℝ) ≤ (982095812893/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245523953223/250000000000 : ℝ) ≤ (radius 8 (37/256 : ℝ)) ∧ (radius 8 (37/256 : ℝ)) ≤ (982095812893/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (37/256 : ℝ)) (245523953223/250000000000 : ℝ) (982095812893/1000000000000 : ℝ) (188382096543/1000000000000 : ℝ) (188382096549/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (37/256 : ℝ)) (245523953223/250000000000 : ℝ) (982095812893/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (37/256 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245523953223/250000000000 : ℝ) (982095812893/1000000000000 : ℝ) (495523953223/500000000000 : ℝ) (991047906447/1000000000000 : ℝ) (991007473681/1000000000000 : ℝ) (495503736841/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (37/256 : ℝ)) 1 (495523953223/500000000000 : ℝ) (991047906447/1000000000000 : ℝ) (991007473681/1000000000000 : ℝ) (495503736841/500000000000 : ℝ) (991027690063/1000000000000 : ℝ) (198205538013/200000000000 : ℝ) (991027689857/1000000000000 : ℝ) (991027689859/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (37/256 : ℝ)) 2 (991027690063/1000000000000 : ℝ) (198205538013/200000000000 : ℝ) (991027689857/1000000000000 : ℝ) (991027689859/1000000000000 : ℝ) (24775692249/25000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (37/256 : ℝ)) 3 (24775692249/25000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (37/256 : ℝ)) 4 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (37/256 : ℝ)) 5 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (37/256 : ℝ)) 6 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (37/256 : ℝ)) 7 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (37/256 : ℝ))) (188382096543/1000000000000 : ℝ) (188382096549/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (37/256 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (188382096543/1000000000000 : ℝ) (188382096549/1000000000000 : ℝ) (594191048271/1000000000000 : ℝ) (23767641931/40000000000 : ℝ) (4340300641/10000000000 : ℝ) (108507516027/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (37/256 : ℝ))) 1 (594191048271/1000000000000 : ℝ) (23767641931/40000000000 : ℝ) (4340300641/10000000000 : ℝ) (108507516027/250000000000 : ℝ) (102822111237/200000000000 : ℝ) (16065954881/31250000000 : ℝ) (253917692751/500000000000 : ℝ) (50783538551/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (37/256 : ℝ))) 2 (102822111237/200000000000 : ℝ) (16065954881/31250000000 : ℝ) (253917692751/500000000000 : ℝ) (50783538551/100000000000 : ℝ) (510972970843/1000000000000 : ℝ) (510972970851/1000000000000 : ℝ) (127740834429/250000000000 : ℝ) (20438533509/40000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (37/256 : ℝ))) 3 (510972970843/1000000000000 : ℝ) (510972970851/1000000000000 : ℝ) (127740834429/250000000000 : ℝ) (20438533509/40000000000 : ℝ) (510968154279/1000000000000 : ℝ) (31935509643/62500000000 : ℝ) (31935509641/62500000000 : ℝ) (255484077133/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (37/256 : ℝ))) 4 (510968154279/1000000000000 : ℝ) (31935509643/62500000000 : ℝ) (31935509641/62500000000 : ℝ) (255484077133/500000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (37/256 : ℝ))) 5 (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (37/256 : ℝ))) 6 (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (37/256 : ℝ))) 7 (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (37/256 : ℝ)) hmem 8 (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (37/256 : ℝ))) hcmem 8 (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (37/256 : ℝ)) (991027689959/1000000000000 : ℝ) (495513844981/500000000000 : ℝ) (510968154267/1000000000000 : ℝ) (510968154277/1000000000000 : ℝ) (809893515551/1000000000000 : ℝ) (80989351557/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1698_exp_lower
  have heNumeric : (1027672599921/500000000000 : ℝ)/4 ≤ Real.exp (-33292527341/50000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027672599921/500000000000 : ℝ)/4 ≤ Real.exp ((295/2048 : ℝ)-(80989351557/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (295/2048 : ℝ) (37/256 : ℝ) (80989351557/100000000000 : ℝ) (1027672599921/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1699; no trusted numerical premise.
theorem cover8_leaf1699_exp_radius : (997736635106050523/1000000000000000000 : ℝ) ≤ Real.exp ((-297/16384 : ℝ)/8) ∧ Real.exp ((-297/16384 : ℝ)/8) ≤ (249434158776512631/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-297/16384 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1699_exp_lower : (920142849247741283/1000000000000000000 : ℝ) ≤ Real.exp ((-665810800567/1000000000000 : ℝ)/8) ∧ Real.exp ((-665810800567/1000000000000 : ℝ)/8) ≤ (230035712311935321/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-665810800567/1000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1699_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256928361717/125000000000 : ℝ) ≤ 4*Real.exp (37/256 : ℝ)*Real.exp (-mu (radius 8 (297/2048 : ℝ))) ∧ (20549/10000 : ℝ) < (256928361717/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (297/2048 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1699_exp_radius
  have hrNumeric : (19640717447/20000000000 : ℝ) ≤ Real.exp (-297/16384 : ℝ) ∧ Real.exp (-297/16384 : ℝ) ≤ (982035872351/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (19640717447/20000000000 : ℝ) ≤ (radius 8 (297/2048 : ℝ)) ∧ (radius 8 (297/2048 : ℝ)) ≤ (982035872351/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (297/2048 : ℝ)) (19640717447/20000000000 : ℝ) (982035872351/1000000000000 : ℝ) (188694317391/1000000000000 : ℝ) (188694317397/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (297/2048 : ℝ)) (19640717447/20000000000 : ℝ) (982035872351/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (297/2048 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (19640717447/20000000000 : ℝ) (982035872351/1000000000000 : ℝ) (39640717447/40000000000 : ℝ) (61938621011/62500000000 : ℝ) (495488615497/500000000000 : ℝ) (247744307749/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (297/2048 : ℝ)) 1 (39640717447/40000000000 : ℝ) (61938621011/62500000000 : ℝ) (495488615497/500000000000 : ℝ) (247744307749/250000000000 : ℝ) (30968674487/31250000000 : ℝ) (495498791793/500000000000 : ℝ) (7927980667/8000000000 : ℝ) (495498791689/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (297/2048 : ℝ)) 2 (30968674487/31250000000 : ℝ) (495498791793/500000000000 : ℝ) (7927980667/8000000000 : ℝ) (495498791689/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (297/2048 : ℝ)) 3 (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (297/2048 : ℝ)) 4 (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (297/2048 : ℝ)) 5 (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (297/2048 : ℝ)) 6 (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (297/2048 : ℝ)) 7 (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (297/2048 : ℝ))) (188694317391/1000000000000 : ℝ) (188694317397/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (297/2048 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (188694317391/1000000000000 : ℝ) (188694317397/1000000000000 : ℝ) (118869431739/200000000000 : ℝ) (594347158699/1000000000000 : ℝ) (86877918343/200000000000 : ℝ) (434389591723/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (297/2048 : ℝ))) 1 (118869431739/200000000000 : ℝ) (594347158699/1000000000000 : ℝ) (86877918343/200000000000 : ℝ) (434389591723/1000000000000 : ℝ) (102873675041/200000000000 : ℝ) (514368375211/1000000000000 : ℝ) (508112408431/1000000000000 : ℝ) (508112408439/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (297/2048 : ℝ))) 2 (102873675041/200000000000 : ℝ) (514368375211/1000000000000 : ℝ) (508112408431/1000000000000 : ℝ) (508112408439/1000000000000 : ℝ) (255620195909/500000000000 : ℝ) (20449615673/40000000000 : ℝ) (51123082257/100000000000 : ℝ) (255615411289/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (297/2048 : ℝ))) 3 (255620195909/500000000000 : ℝ) (20449615673/40000000000 : ℝ) (51123082257/100000000000 : ℝ) (255615411289/500000000000 : ℝ) (255617803597/500000000000 : ℝ) (255617803601/500000000000 : ℝ) (511235607171/1000000000000 : ℝ) (25561780359/50000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (297/2048 : ℝ))) 4 (255617803597/500000000000 : ℝ) (255617803601/500000000000 : ℝ) (511235607171/1000000000000 : ℝ) (25561780359/50000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (297/2048 : ℝ))) 5 (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (297/2048 : ℝ))) 6 (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (297/2048 : ℝ))) 7 (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (297/2048 : ℝ)) hmem 8 (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (297/2048 : ℝ))) hcmem 8 (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (297/2048 : ℝ)) (990997583479/1000000000000 : ℝ) (495498791741/500000000000 : ℝ) (255617803591/500000000000 : ℝ) (511235607191/1000000000000 : ℝ) (810342050549/1000000000000 : ℝ) (810342050567/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1699_exp_lower
  have heNumeric : (256928361717/125000000000 : ℝ)/4 ≤ Real.exp (-665810800567/1000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256928361717/125000000000 : ℝ)/4 ≤ Real.exp ((37/256 : ℝ)-(810342050567/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (37/256 : ℝ) (297/2048 : ℝ) (810342050567/1000000000000 : ℝ) (256928361717/125000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1675_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1675_certificate
#check SmaleRate.Proofs.cover8_leaf1676_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1676_certificate
#check SmaleRate.Proofs.cover8_leaf1677_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1677_certificate
#check SmaleRate.Proofs.cover8_leaf1678_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1678_certificate
#check SmaleRate.Proofs.cover8_leaf1679_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1679_certificate
#check SmaleRate.Proofs.cover8_leaf1680_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1680_certificate
#check SmaleRate.Proofs.cover8_leaf1681_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1681_certificate
#check SmaleRate.Proofs.cover8_leaf1682_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1682_certificate
#check SmaleRate.Proofs.cover8_leaf1683_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1683_certificate
#check SmaleRate.Proofs.cover8_leaf1684_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1684_certificate
#check SmaleRate.Proofs.cover8_leaf1685_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1685_certificate
#check SmaleRate.Proofs.cover8_leaf1686_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1686_certificate
#check SmaleRate.Proofs.cover8_leaf1687_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1687_certificate
#check SmaleRate.Proofs.cover8_leaf1688_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1688_certificate
#check SmaleRate.Proofs.cover8_leaf1689_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1689_certificate
#check SmaleRate.Proofs.cover8_leaf1690_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1690_certificate
#check SmaleRate.Proofs.cover8_leaf1691_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1691_certificate
#check SmaleRate.Proofs.cover8_leaf1692_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1692_certificate
#check SmaleRate.Proofs.cover8_leaf1693_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1693_certificate
#check SmaleRate.Proofs.cover8_leaf1694_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1694_certificate
#check SmaleRate.Proofs.cover8_leaf1695_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1695_certificate
#check SmaleRate.Proofs.cover8_leaf1696_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1696_certificate
#check SmaleRate.Proofs.cover8_leaf1697_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1697_certificate
#check SmaleRate.Proofs.cover8_leaf1698_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1698_certificate
#check SmaleRate.Proofs.cover8_leaf1699_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1699_certificate
