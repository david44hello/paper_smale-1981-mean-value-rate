/- SmaleRate — rational interval-cover certificate.
Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE. -/
module

public import SmaleRate.Proofs.AGMCertificates

@[expose] public section

noncomputable section
namespace SmaleRate.Proofs
open Set Filter

-- Proposed record cover8_leaf1475; no trusted numerical premise.
theorem cover8_leaf1475_exp_radius : (997976088999613461/1000000000000000000 : ℝ) ≤ Real.exp ((-16995/1048576 : ℝ)/8) ∧ Real.exp ((-16995/1048576 : ℝ)/8) ≤ (498988044499806731/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16995/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1475_exp_lower : (2300284992795893/2500000000000000 : ℝ) ≤ Real.exp ((-10656986458111/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656986458111/16000000000000 : ℝ)/8) ≤ (920113997118357201/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656986458111/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1475_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455674133/500000000000 : ℝ) ≤ 4*Real.exp (8497/65536 : ℝ)*Real.exp (-mu (radius 8 (16995/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455674133/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16995/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1475_exp_radius
  have hrNumeric : (983922942949/1000000000000 : ℝ) ≤ Real.exp (-16995/1048576 : ℝ) ∧ Real.exp (-16995/1048576 : ℝ) ≤ (19678458859/20000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983922942949/1000000000000 : ℝ) ≤ (radius 8 (16995/131072 : ℝ)) ∧ (radius 8 (16995/131072 : ℝ)) ≤ (19678458859/20000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16995/131072 : ℝ)) (983922942949/1000000000000 : ℝ) (19678458859/20000000000 : ℝ) (89296755731/500000000000 : ℝ) (178593511469/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16995/131072 : ℝ)) (983922942949/1000000000000 : ℝ) (19678458859/20000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16995/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983922942949/1000000000000 : ℝ) (19678458859/20000000000 : ℝ) (495980735737/500000000000 : ℝ) (39678458859/40000000000 : ℝ) (247982225037/250000000000 : ℝ) (991928900149/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16995/131072 : ℝ)) 1 (495980735737/500000000000 : ℝ) (39678458859/40000000000 : ℝ) (247982225037/250000000000 : ℝ) (991928900149/1000000000000 : ℝ) (991945185811/1000000000000 : ℝ) (247986296453/250000000000 : ℝ) (991945185677/1000000000000 : ℝ) (991945185679/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16995/131072 : ℝ)) 2 (991945185811/1000000000000 : ℝ) (247986296453/250000000000 : ℝ) (991945185677/1000000000000 : ℝ) (991945185679/1000000000000 : ℝ) (61996574109/62500000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16995/131072 : ℝ)) 3 (61996574109/62500000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16995/131072 : ℝ)) 4 (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16995/131072 : ℝ)) 5 (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16995/131072 : ℝ)) 6 (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16995/131072 : ℝ)) 7 (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16995/131072 : ℝ))) (89296755731/500000000000 : ℝ) (178593511469/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16995/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89296755731/500000000000 : ℝ) (178593511469/1000000000000 : ℝ) (589296755731/1000000000000 : ℝ) (117859351147/200000000000 : ℝ) (84520651077/200000000000 : ℝ) (211301627697/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16995/131072 : ℝ))) 1 (589296755731/1000000000000 : ℝ) (117859351147/200000000000 : ℝ) (84520651077/200000000000 : ℝ) (211301627697/500000000000 : ℝ) (252975002779/500000000000 : ℝ) (101190001113/200000000000 : ℝ) (499037801533/1000000000000 : ℝ) (499037801541/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16995/131072 : ℝ))) 2 (252975002779/500000000000 : ℝ) (101190001113/200000000000 : ℝ) (499037801533/1000000000000 : ℝ) (499037801541/1000000000000 : ℝ) (100498780709/200000000000 : ℝ) (502493903553/1000000000000 : ℝ) (100496403609/200000000000 : ℝ) (251241009027/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16995/131072 : ℝ))) 3 (100498780709/200000000000 : ℝ) (502493903553/1000000000000 : ℝ) (100496403609/200000000000 : ℝ) (251241009027/500000000000 : ℝ) (100497592159/200000000000 : ℝ) (125621990201/250000000000 : ℝ) (502487960759/1000000000000 : ℝ) (502487960769/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16995/131072 : ℝ))) 4 (100497592159/200000000000 : ℝ) (125621990201/250000000000 : ℝ) (502487960759/1000000000000 : ℝ) (502487960769/1000000000000 : ℝ) (502487960777/1000000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16995/131072 : ℝ))) 5 (502487960777/1000000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16995/131072 : ℝ))) 6 (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16995/131072 : ℝ))) 7 (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16995/131072 : ℝ)) hmem 8 (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16995/131072 : ℝ))) hcmem 8 (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16995/131072 : ℝ)) (991945185743/1000000000000 : ℝ) (495972592873/500000000000 : ℝ) (62810995097/125000000000 : ℝ) (502487960787/1000000000000 : ℝ) (31828623371/40000000000 : ℝ) (99464448037/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1475_exp_lower
  have heNumeric : (1027455674133/500000000000 : ℝ)/4 ≤ Real.exp (-10656986458111/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455674133/500000000000 : ℝ)/4 ≤ Real.exp ((8497/65536 : ℝ)-(99464448037/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8497/65536 : ℝ) (16995/131072 : ℝ) (99464448037/125000000000 : ℝ) (1027455674133/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1476; no trusted numerical premise.
theorem cover8_leaf1476_exp_radius : (498987985015799997/500000000000000000 : ℝ) ≤ Real.exp ((-4249/262144 : ℝ)/8) ∧ Real.exp ((-4249/262144 : ℝ)/8) ≤ (199595194006319999/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4249/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1476_exp_lower : (920114006320593447/1000000000000000000 : ℝ) ≤ Real.exp ((-21313970355917/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313970355917/32000000000000 : ℝ)/8) ≤ (115014250790074181/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313970355917/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1476_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455756339/500000000000 : ℝ) ≤ 4*Real.exp (16995/131072 : ℝ)*Real.exp (-mu (radius 8 (4249/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455756339/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4249/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1476_exp_radius
  have hrNumeric : (983922004607/1000000000000 : ℝ) ≤ Real.exp (-4249/262144 : ℝ) ∧ Real.exp (-4249/262144 : ℝ) ≤ (7686890661/7812500000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983922004607/1000000000000 : ℝ) ≤ (radius 8 (4249/32768 : ℝ)) ∧ (radius 8 (4249/32768 : ℝ)) ≤ (7686890661/7812500000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4249/32768 : ℝ)) (983922004607/1000000000000 : ℝ) (7686890661/7812500000 : ℝ) (178598680981/1000000000000 : ℝ) (178598680987/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4249/32768 : ℝ)) (983922004607/1000000000000 : ℝ) (7686890661/7812500000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4249/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983922004607/1000000000000 : ℝ) (7686890661/7812500000 : ℝ) (991961002303/1000000000000 : ℝ) (15499390661/15625000000 : ℝ) (991928427159/1000000000000 : ℝ) (24798210679/25000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4249/32768 : ℝ)) 1 (991961002303/1000000000000 : ℝ) (15499390661/15625000000 : ℝ) (991928427159/1000000000000 : ℝ) (24798210679/25000000000 : ℝ) (991944714731/1000000000000 : ℝ) (247986178683/250000000000 : ℝ) (991944714597/1000000000000 : ℝ) (991944714599/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4249/32768 : ℝ)) 2 (991944714731/1000000000000 : ℝ) (247986178683/250000000000 : ℝ) (991944714597/1000000000000 : ℝ) (991944714599/1000000000000 : ℝ) (123993089333/125000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4249/32768 : ℝ)) 3 (123993089333/125000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4249/32768 : ℝ)) 4 (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4249/32768 : ℝ)) 5 (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4249/32768 : ℝ)) 6 (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4249/32768 : ℝ)) 7 (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4249/32768 : ℝ))) (178598680981/1000000000000 : ℝ) (178598680987/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4249/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178598680981/1000000000000 : ℝ) (178598680987/1000000000000 : ℝ) (58929934049/100000000000 : ℝ) (294649670247/500000000000 : ℝ) (422609371619/1000000000000 : ℝ) (105652342907/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4249/32768 : ℝ))) 1 (58929934049/100000000000 : ℝ) (294649670247/500000000000 : ℝ) (422609371619/1000000000000 : ℝ) (105652342907/250000000000 : ℝ) (252977178027/500000000000 : ℝ) (505954356061/1000000000000 : ℝ) (499042507187/1000000000000 : ℝ) (99808501439/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4249/32768 : ℝ))) 2 (252977178027/500000000000 : ℝ) (505954356061/1000000000000 : ℝ) (499042507187/1000000000000 : ℝ) (99808501439/200000000000 : ℝ) (25124921581/50000000000 : ℝ) (125624607907/250000000000 : ℝ) (502486547449/1000000000000 : ℝ) (502486547457/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4249/32768 : ℝ))) 3 (25124921581/50000000000 : ℝ) (125624607907/250000000000 : ℝ) (502486547449/1000000000000 : ℝ) (502486547457/1000000000000 : ℝ) (251246244767/500000000000 : ℝ) (502492489543/1000000000000 : ℝ) (502492489499/1000000000000 : ℝ) (125623122377/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4249/32768 : ℝ))) 4 (251246244767/500000000000 : ℝ) (502492489543/1000000000000 : ℝ) (502492489499/1000000000000 : ℝ) (125623122377/250000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4249/32768 : ℝ))) 5 (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4249/32768 : ℝ))) 6 (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4249/32768 : ℝ))) 7 (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4249/32768 : ℝ)) hmem 8 (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4249/32768 : ℝ))) hcmem 8 (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4249/32768 : ℝ)) (991944714663/1000000000000 : ℝ) (495972357333/500000000000 : ℝ) (125623122379/250000000000 : ℝ) (251246244763/500000000000 : ℝ) (397861566831/500000000000 : ℝ) (795723133681/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1476_exp_lower
  have heNumeric : (1027455756339/500000000000 : ℝ)/4 ≤ Real.exp (-21313970355917/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455756339/500000000000 : ℝ)/4 ≤ Real.exp ((16995/131072 : ℝ)-(795723133681/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16995/131072 : ℝ) (4249/32768 : ℝ) (795723133681/1000000000000 : ℝ) (1027455756339/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1477; no trusted numerical premise.
theorem cover8_leaf1477_exp_radius : (997975851063600709/1000000000000000000 : ℝ) ≤ Real.exp ((-16997/1048576 : ℝ)/8) ∧ Real.exp ((-16997/1048576 : ℝ)/8) ≤ (99797585106360071/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16997/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1477_exp_lower : (449274421659023/488281250000000 : ℝ) ≤ Real.exp ((-5328491946479/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328491946479/8000000000000 : ℝ)/8) ≤ (184022803111535821/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328491946479/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1477_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027455838857/500000000000 : ℝ) ≤ 4*Real.exp (4249/32768 : ℝ)*Real.exp (-mu (radius 8 (16997/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027455838857/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16997/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1477_exp_radius
  have hrNumeric : (491960533133/500000000000 : ℝ) ≤ Real.exp (-16997/1048576 : ℝ) ∧ Real.exp (-16997/1048576 : ℝ) ≤ (983921066267/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491960533133/500000000000 : ℝ) ≤ (radius 8 (16997/131072 : ℝ)) ∧ (radius 8 (16997/131072 : ℝ)) ≤ (983921066267/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16997/131072 : ℝ)) (491960533133/500000000000 : ℝ) (983921066267/1000000000000 : ℝ) (178603850339/1000000000000 : ℝ) (35720770069/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16997/131072 : ℝ)) (491960533133/500000000000 : ℝ) (983921066267/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16997/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491960533133/500000000000 : ℝ) (983921066267/1000000000000 : ℝ) (991960533133/1000000000000 : ℝ) (495980266567/500000000000 : ℝ) (991927954171/1000000000000 : ℝ) (247981988543/250000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16997/131072 : ℝ)) 1 (991960533133/1000000000000 : ℝ) (495980266567/500000000000 : ℝ) (991927954171/1000000000000 : ℝ) (247981988543/250000000000 : ℝ) (247986060913/250000000000 : ℝ) (991944243653/1000000000000 : ℝ) (495972121759/500000000000 : ℝ) (3099825761/3125000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16997/131072 : ℝ)) 2 (247986060913/250000000000 : ℝ) (991944243653/1000000000000 : ℝ) (495972121759/500000000000 : ℝ) (3099825761/3125000000 : ℝ) (198388848717/200000000000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16997/131072 : ℝ)) 3 (198388848717/200000000000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16997/131072 : ℝ)) 4 (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16997/131072 : ℝ)) 5 (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16997/131072 : ℝ)) 6 (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16997/131072 : ℝ)) 7 (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16997/131072 : ℝ))) (178603850339/1000000000000 : ℝ) (35720770069/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16997/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178603850339/1000000000000 : ℝ) (35720770069/200000000000 : ℝ) (589301925169/1000000000000 : ℝ) (589301925173/1000000000000 : ℝ) (16904619503/40000000000 : ℝ) (422615487583/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16997/131072 : ℝ))) 1 (589301925169/1000000000000 : ℝ) (589301925173/1000000000000 : ℝ) (16904619503/40000000000 : ℝ) (422615487583/1000000000000 : ℝ) (126489676593/250000000000 : ℝ) (252979353189/500000000000 : ℝ) (49904721263/100000000000 : ℝ) (499047212637/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16997/131072 : ℝ))) 2 (126489676593/250000000000 : ℝ) (252979353189/500000000000 : ℝ) (49904721263/100000000000 : ℝ) (499047212637/1000000000000 : ℝ) (502502959501/1000000000000 : ℝ) (125625739877/250000000000 : ℝ) (502491076657/1000000000000 : ℝ) (100498215333/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16997/131072 : ℝ))) 3 (502502959501/1000000000000 : ℝ) (125625739877/250000000000 : ℝ) (502491076657/1000000000000 : ℝ) (100498215333/200000000000 : ℝ) (502497018079/1000000000000 : ℝ) (502497018087/1000000000000 : ℝ) (502497018043/1000000000000 : ℝ) (125624254513/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16997/131072 : ℝ))) 4 (502497018079/1000000000000 : ℝ) (502497018087/1000000000000 : ℝ) (502497018043/1000000000000 : ℝ) (125624254513/250000000000 : ℝ) (502497018061/1000000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16997/131072 : ℝ))) 5 (502497018061/1000000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16997/131072 : ℝ))) 6 (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16997/131072 : ℝ))) 7 (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16997/131072 : ℝ)) hmem 8 (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16997/131072 : ℝ))) hcmem 8 (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16997/131072 : ℝ)) (7749564403/7812500000 : ℝ) (991944243587/1000000000000 : ℝ) (25124850903/50000000000 : ℝ) (50249701807/100000000000 : ℝ) (99466335343/125000000000 : ℝ) (795730682763/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1477_exp_lower
  have heNumeric : (1027455838857/500000000000 : ℝ)/4 ≤ Real.exp (-5328491946479/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027455838857/500000000000 : ℝ)/4 ≤ Real.exp ((4249/32768 : ℝ)-(795730682763/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4249/32768 : ℝ) (16997/131072 : ℝ) (795730682763/1000000000000 : ℝ) (1027455838857/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1478; no trusted numerical premise.
theorem cover8_leaf1478_exp_radius : (498987866047807803/500000000000000000 : ℝ) ≤ Real.exp ((-8499/524288 : ℝ)/8) ∧ Real.exp ((-8499/524288 : ℝ)/8) ≤ (997975732095615607/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8499/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1478_exp_lower : (920114024830074229/1000000000000000000 : ℝ) ≤ Real.exp ((-21313965206091/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313965206091/32000000000000 : ℝ)/8) ≤ (92011402483007423/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313965206091/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1478_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (102745592169/50000000000 : ℝ) ≤ 4*Real.exp (16997/131072 : ℝ)*Real.exp (-mu (radius 8 (8499/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (102745592169/50000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8499/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1478_exp_radius
  have hrNumeric : (983920127927/1000000000000 : ℝ) ≤ Real.exp (-8499/524288 : ℝ) ∧ Real.exp (-8499/524288 : ℝ) ≤ (122990015991/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983920127927/1000000000000 : ℝ) ≤ (radius 8 (8499/65536 : ℝ)) ∧ (radius 8 (8499/65536 : ℝ)) ≤ (122990015991/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8499/65536 : ℝ)) (983920127927/1000000000000 : ℝ) (122990015991/125000000000 : ℝ) (178609019531/1000000000000 : ℝ) (89304509769/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8499/65536 : ℝ)) (983920127927/1000000000000 : ℝ) (122990015991/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8499/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983920127927/1000000000000 : ℝ) (122990015991/125000000000 : ℝ) (991960063963/1000000000000 : ℝ) (247990015991/250000000000 : ℝ) (991927481183/1000000000000 : ℝ) (30997733787/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8499/65536 : ℝ)) 1 (991960063963/1000000000000 : ℝ) (247990015991/250000000000 : ℝ) (991927481183/1000000000000 : ℝ) (30997733787/31250000000 : ℝ) (991943772573/1000000000000 : ℝ) (495971886287/500000000000 : ℝ) (991943772439/1000000000000 : ℝ) (991943772441/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8499/65536 : ℝ)) 2 (991943772573/1000000000000 : ℝ) (495971886287/500000000000 : ℝ) (991943772439/1000000000000 : ℝ) (991943772441/1000000000000 : ℝ) (495971886253/500000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8499/65536 : ℝ)) 3 (495971886253/500000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8499/65536 : ℝ)) 4 (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8499/65536 : ℝ)) 5 (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8499/65536 : ℝ)) 6 (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8499/65536 : ℝ)) 7 (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8499/65536 : ℝ))) (178609019531/1000000000000 : ℝ) (89304509769/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8499/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178609019531/1000000000000 : ℝ) (89304509769/500000000000 : ℝ) (117860901953/200000000000 : ℝ) (589304509769/1000000000000 : ℝ) (211310801623/500000000000 : ℝ) (52827700407/125000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8499/65536 : ℝ))) 1 (117860901953/200000000000 : ℝ) (589304509769/1000000000000 : ℝ) (211310801623/500000000000 : ℝ) (52827700407/125000000000 : ℝ) (101192611301/200000000000 : ℝ) (505963056513/1000000000000 : ℝ) (499051917857/1000000000000 : ℝ) (99810383573/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8499/65536 : ℝ))) 2 (101192611301/200000000000 : ℝ) (505963056513/1000000000000 : ℝ) (499051917857/1000000000000 : ℝ) (99810383573/200000000000 : ℝ) (502507487181/1000000000000 : ℝ) (502507487189/1000000000000 : ℝ) (100499121133/200000000000 : ℝ) (251247802837/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8499/65536 : ℝ))) 3 (502507487181/1000000000000 : ℝ) (502507487189/1000000000000 : ℝ) (100499121133/200000000000 : ℝ) (251247802837/500000000000 : ℝ) (502501546423/1000000000000 : ℝ) (7851586663/15625000000 : ℝ) (502501546387/1000000000000 : ℝ) (502501546397/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8499/65536 : ℝ))) 4 (502501546423/1000000000000 : ℝ) (7851586663/15625000000 : ℝ) (502501546387/1000000000000 : ℝ) (502501546397/1000000000000 : ℝ) (100500309281/200000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8499/65536 : ℝ))) 5 (100500309281/200000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8499/65536 : ℝ))) 6 (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8499/65536 : ℝ))) 7 (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8499/65536 : ℝ)) hmem 8 (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8499/65536 : ℝ))) hcmem 8 (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8499/65536 : ℝ)) (198388754501/200000000000 : ℝ) (247985943127/250000000000 : ℝ) (125625386601/250000000000 : ℝ) (100500309283/200000000000 : ℝ) (795738231517/1000000000000 : ℝ) (397869115769/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1478_exp_lower
  have heNumeric : (102745592169/50000000000 : ℝ)/4 ≤ Real.exp (-21313965206091/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (102745592169/50000000000 : ℝ)/4 ≤ Real.exp ((16997/131072 : ℝ)-(397869115769/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16997/131072 : ℝ) (8499/65536 : ℝ) (397869115769/500000000000 : ℝ) (102745592169/50000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1479; no trusted numerical premise.
theorem cover8_leaf1479_exp_radius : (199595122625528937/200000000000000000 : ℝ) ≤ Real.exp ((-16999/1048576 : ℝ)/8) ∧ Real.exp ((-16999/1048576 : ℝ)/8) ≤ (498987806563822343/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-16999/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1479_exp_lower : (460057017068199327/500000000000000000 : ℝ) ≤ Real.exp ((-10656981308413/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656981308413/16000000000000 : ℝ)/8) ≤ (184022806827279731/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656981308413/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1479_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513728002413/250000000000 : ℝ) ≤ 4*Real.exp (8499/65536 : ℝ)*Real.exp (-mu (radius 8 (16999/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513728002413/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (16999/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1479_exp_radius
  have hrNumeric : (245979797397/250000000000 : ℝ) ≤ Real.exp (-16999/1048576 : ℝ) ∧ Real.exp (-16999/1048576 : ℝ) ≤ (983919189589/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (245979797397/250000000000 : ℝ) ≤ (radius 8 (16999/131072 : ℝ)) ∧ (radius 8 (16999/131072 : ℝ)) ≤ (983919189589/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (16999/131072 : ℝ)) (245979797397/250000000000 : ℝ) (983919189589/1000000000000 : ℝ) (17861418857/100000000000 : ℝ) (5581693393/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (16999/131072 : ℝ)) (245979797397/250000000000 : ℝ) (983919189589/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (16999/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (245979797397/250000000000 : ℝ) (983919189589/1000000000000 : ℝ) (495979797397/500000000000 : ℝ) (198391918959/200000000000 : ℝ) (198385401639/200000000000 : ℝ) (991927008197/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (16999/131072 : ℝ)) 1 (495979797397/500000000000 : ℝ) (198391918959/200000000000 : ℝ) (198385401639/200000000000 : ℝ) (991927008197/1000000000000 : ℝ) (495971650747/500000000000 : ℝ) (123992912687/125000000000 : ℝ) (12399291267/12500000000 : ℝ) (991943301363/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (16999/131072 : ℝ)) 2 (495971650747/500000000000 : ℝ) (123992912687/125000000000 : ℝ) (12399291267/12500000000 : ℝ) (991943301363/1000000000000 : ℝ) (991943301427/1000000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (16999/131072 : ℝ)) 3 (991943301427/1000000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (16999/131072 : ℝ)) 4 (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (16999/131072 : ℝ)) 5 (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (16999/131072 : ℝ)) 6 (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (16999/131072 : ℝ)) 7 (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (16999/131072 : ℝ))) (17861418857/100000000000 : ℝ) (5581693393/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (16999/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17861418857/100000000000 : ℝ) (5581693393/31250000000 : ℝ) (117861418857/200000000000 : ℝ) (36831693393/62500000000 : ℝ) (52828464831/125000000000 : ℝ) (825444763/1953125000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (16999/131072 : ℝ))) 1 (117861418857/200000000000 : ℝ) (36831693393/62500000000 : ℝ) (52828464831/125000000000 : ℝ) (825444763/1953125000 : ℝ) (252983703233/500000000000 : ℝ) (63245925809/125000000000 : ℝ) (3119103893/6250000000 : ℝ) (499056622887/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (16999/131072 : ℝ))) 2 (252983703233/500000000000 : ℝ) (63245925809/125000000000 : ℝ) (3119103893/6250000000 : ℝ) (499056622887/1000000000000 : ℝ) (502512014673/1000000000000 : ℝ) (12562800367/25000000000 : ℝ) (100500026897/200000000000 : ℝ) (502500134493/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (16999/131072 : ℝ))) 3 (502512014673/1000000000000 : ℝ) (12562800367/25000000000 : ℝ) (100500026897/200000000000 : ℝ) (502500134493/1000000000000 : ℝ) (502506074579/1000000000000 : ℝ) (502506074587/1000000000000 : ℝ) (502506074543/1000000000000 : ℝ) (62813259319/125000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (16999/131072 : ℝ))) 4 (502506074579/1000000000000 : ℝ) (502506074587/1000000000000 : ℝ) (502506074543/1000000000000 : ℝ) (62813259319/125000000000 : ℝ) (502506074561/1000000000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (16999/131072 : ℝ))) 5 (502506074561/1000000000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (16999/131072 : ℝ))) 6 (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (16999/131072 : ℝ))) 7 (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (16999/131072 : ℝ)) hmem 8 (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (16999/131072 : ℝ))) hcmem 8 (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (16999/131072 : ℝ)) (495971650713/500000000000 : ℝ) (99194330143/100000000000 : ℝ) (1570331483/3125000000 : ℝ) (50250607457/100000000000 : ℝ) (397872889999/500000000000 : ℝ) (397872890009/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1479_exp_lower
  have heNumeric : (513728002413/250000000000 : ℝ)/4 ≤ Real.exp (-10656981308413/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513728002413/250000000000 : ℝ)/4 ≤ Real.exp ((8499/65536 : ℝ)-(397872890009/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8499/65536 : ℝ) (16999/131072 : ℝ) (397872890009/500000000000 : ℝ) (513728002413/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1480; no trusted numerical premise.
theorem cover8_leaf1480_exp_radius : (498987747079843973/500000000000000000 : ℝ) ≤ Real.exp ((-2125/131072 : ℝ)/8) ∧ Real.exp ((-2125/131072 : ℝ)/8) ≤ (997975494159687947/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2125/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1480_exp_lower : (920114043477572491/1000000000000000000 : ℝ) ≤ Real.exp ((-4262792003573/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262792003573/6400000000000 : ℝ)/8) ≤ (230028510869393123/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262792003573/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1480_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912176547/1000000000000 : ℝ) ≤ 4*Real.exp (16999/131072 : ℝ)*Real.exp (-mu (radius 8 (2125/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912176547/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2125/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1480_exp_radius
  have hrNumeric : (787134601/800000000 : ℝ) ≤ Real.exp (-2125/131072 : ℝ) ∧ Real.exp (-2125/131072 : ℝ) ≤ (983918251251/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (787134601/800000000 : ℝ) ≤ (radius 8 (2125/16384 : ℝ)) ∧ (radius 8 (2125/16384 : ℝ)) ≤ (983918251251/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2125/16384 : ℝ)) (787134601/800000000 : ℝ) (983918251251/1000000000000 : ℝ) (22327419681/125000000000 : ℝ) (89309678727/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2125/16384 : ℝ)) (787134601/800000000 : ℝ) (983918251251/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2125/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (787134601/800000000 : ℝ) (983918251251/1000000000000 : ℝ) (1587134601/1600000000 : ℝ) (495979562813/500000000000 : ℝ) (123990816901/125000000000 : ℝ) (991926535209/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2125/16384 : ℝ)) 1 (1587134601/1600000000 : ℝ) (495979562813/500000000000 : ℝ) (123990816901/125000000000 : ℝ) (991926535209/1000000000000 : ℝ) (61996426901/62500000000 : ℝ) (495971415209/500000000000 : ℝ) (495971415141/500000000000 : ℝ) (247985707571/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2125/16384 : ℝ)) 2 (61996426901/62500000000 : ℝ) (495971415209/500000000000 : ℝ) (495971415141/500000000000 : ℝ) (247985707571/250000000000 : ℝ) (991942830349/1000000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2125/16384 : ℝ)) 3 (991942830349/1000000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2125/16384 : ℝ)) 4 (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2125/16384 : ℝ)) 5 (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2125/16384 : ℝ)) 6 (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2125/16384 : ℝ)) 7 (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2125/16384 : ℝ))) (22327419681/125000000000 : ℝ) (89309678727/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2125/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (22327419681/125000000000 : ℝ) (89309678727/500000000000 : ℝ) (147327419681/250000000000 : ℝ) (589309678727/1000000000000 : ℝ) (422633833771/1000000000000 : ℝ) (422633833779/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2125/16384 : ℝ))) 1 (147327419681/250000000000 : ℝ) (589309678727/1000000000000 : ℝ) (422633833771/1000000000000 : ℝ) (422633833779/1000000000000 : ℝ) (505971756247/1000000000000 : ℝ) (505971756253/1000000000000 : ℝ) (499061327691/1000000000000 : ℝ) (249530663849/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2125/16384 : ℝ))) 2 (505971756247/1000000000000 : ℝ) (505971756253/1000000000000 : ℝ) (499061327691/1000000000000 : ℝ) (249530663849/500000000000 : ℝ) (502516541969/1000000000000 : ℝ) (62814567747/125000000000 : ℝ) (502504663109/1000000000000 : ℝ) (125626165779/250000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2125/16384 : ℝ))) 3 (502516541969/1000000000000 : ℝ) (62814567747/125000000000 : ℝ) (502504663109/1000000000000 : ℝ) (125626165779/250000000000 : ℝ) (502510602539/1000000000000 : ℝ) (251255301273/500000000000 : ℝ) (502510602503/1000000000000 : ℝ) (502510602511/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2125/16384 : ℝ))) 4 (502510602539/1000000000000 : ℝ) (251255301273/500000000000 : ℝ) (502510602503/1000000000000 : ℝ) (502510602511/1000000000000 : ℝ) (502510602521/1000000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2125/16384 : ℝ))) 5 (502510602521/1000000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2125/16384 : ℝ))) 6 (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2125/16384 : ℝ))) 7 (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2125/16384 : ℝ)) hmem 8 (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2125/16384 : ℝ))) hcmem 8 (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2125/16384 : ℝ)) (247985707587/250000000000 : ℝ) (991942830351/1000000000000 : ℝ) (12562765063/25000000000 : ℝ) (502510602529/1000000000000 : ℝ) (795753328177/1000000000000 : ℝ) (159150665639/200000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1480_exp_lower
  have heNumeric : (2054912176547/1000000000000 : ℝ)/4 ≤ Real.exp (-4262792003573/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912176547/1000000000000 : ℝ)/4 ≤ Real.exp ((16999/131072 : ℝ)-(159150665639/200000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (16999/131072 : ℝ) (2125/16384 : ℝ) (159150665639/200000000000 : ℝ) (2054912176547/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1481; no trusted numerical premise.
theorem cover8_leaf1481_exp_radius : (997975375191745389/1000000000000000000 : ℝ) ≤ Real.exp ((-17001/1048576 : ℝ)/8) ∧ Real.exp ((-17001/1048576 : ℝ)/8) ≤ (99797537519174539/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17001/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1481_exp_lower : (920114052852445601/1000000000000000000 : ℝ) ≤ Real.exp ((-2664244676191/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664244676191/4000000000000 : ℝ)/8) ≤ (460057026426222801/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664244676191/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1481_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513728086011/250000000000 : ℝ) ≤ 4*Real.exp (2125/16384 : ℝ)*Real.exp (-mu (radius 8 (17001/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513728086011/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17001/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1481_exp_radius
  have hrNumeric : (61494832057/62500000000 : ℝ) ≤ Real.exp (-17001/1048576 : ℝ) ∧ Real.exp (-17001/1048576 : ℝ) ≤ (983917312913/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61494832057/62500000000 : ℝ) ≤ (radius 8 (17001/131072 : ℝ)) ∧ (radius 8 (17001/131072 : ℝ)) ≤ (983917312913/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17001/131072 : ℝ)) (61494832057/62500000000 : ℝ) (983917312913/1000000000000 : ℝ) (178624526171/1000000000000 : ℝ) (89312263089/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17001/131072 : ℝ)) (61494832057/62500000000 : ℝ) (983917312913/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17001/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61494832057/62500000000 : ℝ) (983917312913/1000000000000 : ℝ) (123994832057/125000000000 : ℝ) (991958656457/1000000000000 : ℝ) (49596303111/50000000000 : ℝ) (991926062221/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17001/131072 : ℝ)) 1 (123994832057/125000000000 : ℝ) (991958656457/1000000000000 : ℝ) (49596303111/50000000000 : ℝ) (991926062221/1000000000000 : ℝ) (495971179669/500000000000 : ℝ) (991942359339/1000000000000 : ℝ) (247985589801/250000000000 : ℝ) (495971179603/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17001/131072 : ℝ)) 2 (495971179669/500000000000 : ℝ) (991942359339/1000000000000 : ℝ) (247985589801/250000000000 : ℝ) (495971179603/500000000000 : ℝ) (991942359271/1000000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17001/131072 : ℝ)) 3 (991942359271/1000000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17001/131072 : ℝ)) 4 (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17001/131072 : ℝ)) 5 (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17001/131072 : ℝ)) 6 (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17001/131072 : ℝ)) 7 (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17001/131072 : ℝ))) (178624526171/1000000000000 : ℝ) (89312263089/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17001/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178624526171/1000000000000 : ℝ) (89312263089/500000000000 : ℝ) (117862452617/200000000000 : ℝ) (589312263089/1000000000000 : ℝ) (422639948621/1000000000000 : ℝ) (422639948631/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17001/131072 : ℝ))) 1 (117862452617/200000000000 : ℝ) (589312263089/1000000000000 : ℝ) (422639948621/1000000000000 : ℝ) (422639948631/1000000000000 : ℝ) (505976105853/1000000000000 : ℝ) (25298805293/50000000000 : ℝ) (62383254037/125000000000 : ℝ) (31191627019/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17001/131072 : ℝ))) 2 (505976105853/1000000000000 : ℝ) (25298805293/50000000000 : ℝ) (62383254037/125000000000 : ℝ) (31191627019/62500000000 : ℝ) (251260534537/500000000000 : ℝ) (251260534541/500000000000 : ℝ) (251254595771/500000000000 : ℝ) (10050183831/20000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17001/131072 : ℝ))) 3 (251260534537/500000000000 : ℝ) (251260534541/500000000000 : ℝ) (251254595771/500000000000 : ℝ) (10050183831/20000000000 : ℝ) (125628782577/250000000000 : ℝ) (125628782579/250000000000 : ℝ) (15703597821/31250000000 : ℝ) (502515130281/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17001/131072 : ℝ))) 4 (125628782577/250000000000 : ℝ) (125628782579/250000000000 : ℝ) (15703597821/31250000000 : ℝ) (502515130281/1000000000000 : ℝ) (50251513029/100000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17001/131072 : ℝ))) 5 (50251513029/100000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17001/131072 : ℝ))) 6 (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17001/131072 : ℝ))) 7 (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17001/131072 : ℝ)) hmem 8 (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17001/131072 : ℝ))) hcmem 8 (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17001/131072 : ℝ)) (99194235927/100000000000 : ℝ) (991942359273/1000000000000 : ℝ) (502515130289/1000000000000 : ℝ) (502515130299/1000000000000 : ℝ) (39788043803/50000000000 : ℝ) (795760876079/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1481_exp_lower
  have heNumeric : (513728086011/250000000000 : ℝ)/4 ≤ Real.exp (-2664244676191/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513728086011/250000000000 : ℝ)/4 ≤ Real.exp ((2125/16384 : ℝ)-(795760876079/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2125/16384 : ℝ) (17001/131072 : ℝ) (795760876079/1000000000000 : ℝ) (513728086011/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1482; no trusted numerical premise.
theorem cover8_leaf1482_exp_radius : (498987628111908507/500000000000000000 : ℝ) ≤ Real.exp ((-8501/524288 : ℝ)/8) ∧ Real.exp ((-8501/524288 : ℝ)/8) ≤ (199595051244763403/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8501/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1482_exp_lower : (920114062262628183/1000000000000000000 : ℝ) ≤ Real.exp ((-21313954791367/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313954791367/32000000000000 : ℝ)/8) ≤ (115014257782828523/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313954791367/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1482_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513728128043/250000000000 : ℝ) ≤ 4*Real.exp (17001/131072 : ℝ)*Real.exp (-mu (radius 8 (8501/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (513728128043/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8501/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1482_exp_radius
  have hrNumeric : (61494773411/62500000000 : ℝ) ≤ Real.exp (-8501/524288 : ℝ) ∧ Real.exp (-8501/524288 : ℝ) ≤ (983916374577/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (61494773411/62500000000 : ℝ) ≤ (radius 8 (8501/65536 : ℝ)) ∧ (radius 8 (8501/65536 : ℝ)) ≤ (983916374577/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8501/65536 : ℝ)) (61494773411/62500000000 : ℝ) (983916374577/1000000000000 : ℝ) (178629694729/1000000000000 : ℝ) (11164355921/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8501/65536 : ℝ)) (61494773411/62500000000 : ℝ) (983916374577/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8501/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (61494773411/62500000000 : ℝ) (983916374577/1000000000000 : ℝ) (123994773411/125000000000 : ℝ) (991958187289/1000000000000 : ℝ) (991925589233/1000000000000 : ℝ) (495962794617/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8501/65536 : ℝ)) 1 (123994773411/125000000000 : ℝ) (991958187289/1000000000000 : ℝ) (991925589233/1000000000000 : ℝ) (495962794617/500000000000 : ℝ) (49597094413/50000000000 : ℝ) (495970944131/500000000000 : ℝ) (495970944063/500000000000 : ℝ) (7749546001/7812500000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8501/65536 : ℝ)) 2 (49597094413/50000000000 : ℝ) (495970944131/500000000000 : ℝ) (495970944063/500000000000 : ℝ) (7749546001/7812500000 : ℝ) (991941888193/1000000000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8501/65536 : ℝ)) 3 (991941888193/1000000000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8501/65536 : ℝ)) 4 (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8501/65536 : ℝ)) 5 (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8501/65536 : ℝ)) 6 (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8501/65536 : ℝ)) 7 (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8501/65536 : ℝ))) (178629694729/1000000000000 : ℝ) (11164355921/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8501/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178629694729/1000000000000 : ℝ) (11164355921/62500000000 : ℝ) (147328711841/250000000000 : ℝ) (73664355921/125000000000 : ℝ) (105661515797/250000000000 : ℝ) (211323031599/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8501/65536 : ℝ))) 1 (147328711841/250000000000 : ℝ) (73664355921/125000000000 : ℝ) (105661515797/250000000000 : ℝ) (211323031599/500000000000 : ℝ) (126495113819/250000000000 : ℝ) (505980455283/1000000000000 : ℝ) (249535368343/500000000000 : ℝ) (249535368347/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8501/65536 : ℝ))) 2 (126495113819/250000000000 : ℝ) (505980455283/1000000000000 : ℝ) (249535368343/500000000000 : ℝ) (249535368347/500000000000 : ℝ) (502525595981/1000000000000 : ℝ) (502525595989/1000000000000 : ℝ) (15703553743/31250000000 : ℝ) (62814214973/125000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8501/65536 : ℝ))) 3 (502525595981/1000000000000 : ℝ) (502525595989/1000000000000 : ℝ) (15703553743/31250000000 : ℝ) (62814214973/125000000000 : ℝ) (251259828939/500000000000 : ℝ) (502519657887/1000000000000 : ℝ) (502519657843/1000000000000 : ℝ) (125629914463/250000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8501/65536 : ℝ))) 4 (251259828939/500000000000 : ℝ) (502519657887/1000000000000 : ℝ) (502519657843/1000000000000 : ℝ) (125629914463/250000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8501/65536 : ℝ))) 5 (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8501/65536 : ℝ))) 6 (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8501/65536 : ℝ))) 7 (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8501/65536 : ℝ)) hmem 8 (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8501/65536 : ℝ))) hcmem 8 (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8501/65536 : ℝ)) (15499092003/15625000000 : ℝ) (198388377639/200000000000 : ℝ) (25125982893/50000000000 : ℝ) (50251965787/100000000000 : ℝ) (795768423637/1000000000000 : ℝ) (99471052957/125000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1482_exp_lower
  have heNumeric : (513728128043/250000000000 : ℝ)/4 ≤ Real.exp (-21313954791367/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513728128043/250000000000 : ℝ)/4 ≤ Real.exp ((17001/131072 : ℝ)-(99471052957/125000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17001/131072 : ℝ) (8501/65536 : ℝ) (99471052957/125000000000 : ℝ) (513728128043/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1483; no trusted numerical premise.
theorem cover8_leaf1483_exp_radius : (997975137255902821/1000000000000000000 : ℝ) ≤ Real.exp ((-17003/1048576 : ℝ)/8) ∧ Real.exp ((-17003/1048576 : ℝ)/8) ≤ (498987568627951411/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17003/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1483_exp_lower : (230028517926943799/250000000000000000 : ℝ) ≤ Real.exp ((-10656976081739/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656976081739/16000000000000 : ℝ)/8) ≤ (920114071707775197/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656976081739/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1483_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513728170231/250000000000 : ℝ) ≤ 4*Real.exp (8501/65536 : ℝ)*Real.exp (-mu (radius 8 (17003/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513728170231/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17003/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1483_exp_radius
  have hrNumeric : (983915436241/1000000000000 : ℝ) ≤ Real.exp (-17003/1048576 : ℝ) ∧ Real.exp (-17003/1048576 : ℝ) ≤ (491957718121/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983915436241/1000000000000 : ℝ) ≤ (radius 8 (17003/131072 : ℝ)) ∧ (radius 8 (17003/131072 : ℝ)) ≤ (491957718121/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17003/131072 : ℝ)) (983915436241/1000000000000 : ℝ) (491957718121/500000000000 : ℝ) (178634863127/1000000000000 : ℝ) (89317431567/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17003/131072 : ℝ)) (983915436241/1000000000000 : ℝ) (491957718121/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17003/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983915436241/1000000000000 : ℝ) (491957718121/500000000000 : ℝ) (24798942953/25000000000 : ℝ) (991957718121/1000000000000 : ℝ) (495962558123/500000000000 : ℝ) (123990639531/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17003/131072 : ℝ)) 1 (24798942953/25000000000 : ℝ) (991957718121/1000000000000 : ℝ) (495962558123/500000000000 : ℝ) (123990639531/125000000000 : ℝ) (991941417183/1000000000000 : ℝ) (198388283437/200000000000 : ℝ) (991941417049/1000000000000 : ℝ) (991941417051/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17003/131072 : ℝ)) 2 (991941417183/1000000000000 : ℝ) (198388283437/200000000000 : ℝ) (991941417049/1000000000000 : ℝ) (991941417051/1000000000000 : ℝ) (247985354279/250000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17003/131072 : ℝ)) 3 (247985354279/250000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17003/131072 : ℝ)) 4 (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17003/131072 : ℝ)) 5 (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17003/131072 : ℝ)) 6 (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17003/131072 : ℝ)) 7 (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17003/131072 : ℝ))) (178634863127/1000000000000 : ℝ) (89317431567/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17003/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178634863127/1000000000000 : ℝ) (89317431567/500000000000 : ℝ) (589317431563/1000000000000 : ℝ) (589317431567/1000000000000 : ℝ) (211326088739/500000000000 : ℝ) (422652177487/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17003/131072 : ℝ))) 1 (589317431563/1000000000000 : ℝ) (589317431567/1000000000000 : ℝ) (211326088739/500000000000 : ℝ) (422652177487/1000000000000 : ℝ) (12649620113/25000000000 : ℝ) (505984804527/1000000000000 : ℝ) (249537720433/500000000000 : ℝ) (249537720437/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17003/131072 : ℝ))) 2 (12649620113/25000000000 : ℝ) (505984804527/1000000000000 : ℝ) (249537720433/500000000000 : ℝ) (249537720437/500000000000 : ℝ) (502530122693/1000000000000 : ℝ) (502530122701/1000000000000 : ℝ) (100503649563/200000000000 : ℝ) (502518247823/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17003/131072 : ℝ))) 3 (502530122693/1000000000000 : ℝ) (502530122701/1000000000000 : ℝ) (100503649563/200000000000 : ℝ) (502518247823/1000000000000 : ℝ) (251262092627/500000000000 : ℝ) (251262092631/500000000000 : ℝ) (251262092609/500000000000 : ℝ) (502524185227/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17003/131072 : ℝ))) 4 (251262092627/500000000000 : ℝ) (251262092631/500000000000 : ℝ) (251262092609/500000000000 : ℝ) (502524185227/1000000000000 : ℝ) (125631046309/250000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17003/131072 : ℝ))) 5 (125631046309/250000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17003/131072 : ℝ))) 6 (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17003/131072 : ℝ))) 7 (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17003/131072 : ℝ)) hmem 8 (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17003/131072 : ℝ))) hcmem 8 (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17003/131072 : ℝ)) (198388283423/200000000000 : ℝ) (495970708559/500000000000 : ℝ) (100504837047/200000000000 : ℝ) (100504837049/200000000000 : ℝ) (795775970909/1000000000000 : ℝ) (795775970929/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1483_exp_lower
  have heNumeric : (513728170231/250000000000 : ℝ)/4 ≤ Real.exp (-10656976081739/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513728170231/250000000000 : ℝ)/4 ≤ Real.exp ((8501/65536 : ℝ)-(795775970929/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8501/65536 : ℝ) (17003/131072 : ℝ) (795775970929/1000000000000 : ℝ) (513728170231/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1484; no trusted numerical premise.
theorem cover8_leaf1484_exp_radius : (997975018288002811/1000000000000000000 : ℝ) ≤ Real.exp ((-4251/262144 : ℝ)/8) ∧ Real.exp ((-4251/262144 : ℝ)/8) ≤ (249493754572000703/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4251/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1484_exp_lower : (920114081187771627/1000000000000000000 : ℝ) ≤ Real.exp ((-21313949525893/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313949525893/32000000000000 : ℝ)/8) ≤ (230028520296942907/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313949525893/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1484_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054912850299/1000000000000 : ℝ) ≤ 4*Real.exp (17003/131072 : ℝ)*Real.exp (-mu (radius 8 (4251/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054912850299/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4251/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1484_exp_radius
  have hrNumeric : (983914497907/1000000000000 : ℝ) ≤ Real.exp (-4251/262144 : ℝ) ∧ Real.exp (-4251/262144 : ℝ) ≤ (245978624477/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983914497907/1000000000000 : ℝ) ≤ (radius 8 (4251/32768 : ℝ)) ∧ (radius 8 (4251/32768 : ℝ)) ≤ (245978624477/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4251/32768 : ℝ)) (983914497907/1000000000000 : ℝ) (245978624477/250000000000 : ℝ) (89320015683/500000000000 : ℝ) (44660007843/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4251/32768 : ℝ)) (983914497907/1000000000000 : ℝ) (245978624477/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4251/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983914497907/1000000000000 : ℝ) (245978624477/250000000000 : ℝ) (991957248953/1000000000000 : ℝ) (495978624477/500000000000 : ℝ) (49596232163/50000000000 : ℝ) (991924643261/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4251/32768 : ℝ)) 1 (991957248953/1000000000000 : ℝ) (495978624477/500000000000 : ℝ) (49596232163/50000000000 : ℝ) (991924643261/1000000000000 : ℝ) (495970473053/500000000000 : ℝ) (247985236527/250000000000 : ℝ) (247985236493/250000000000 : ℝ) (495970472987/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4251/32768 : ℝ)) 2 (495970473053/500000000000 : ℝ) (247985236527/250000000000 : ℝ) (247985236493/250000000000 : ℝ) (495970472987/500000000000 : ℝ) (991940946039/1000000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4251/32768 : ℝ)) 3 (991940946039/1000000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4251/32768 : ℝ)) 4 (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4251/32768 : ℝ)) 5 (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4251/32768 : ℝ)) 6 (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4251/32768 : ℝ)) 7 (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4251/32768 : ℝ))) (89320015683/500000000000 : ℝ) (44660007843/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4251/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89320015683/500000000000 : ℝ) (44660007843/250000000000 : ℝ) (589320015683/1000000000000 : ℝ) (294660007843/500000000000 : ℝ) (42265829149/100000000000 : ℝ) (211329145749/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4251/32768 : ℝ))) 1 (589320015683/1000000000000 : ℝ) (294660007843/500000000000 : ℝ) (42265829149/100000000000 : ℝ) (211329145749/500000000000 : ℝ) (252994576793/500000000000 : ℝ) (63248644199/125000000000 : ℝ) (99816028967/200000000000 : ℝ) (249540072421/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4251/32768 : ℝ))) 2 (252994576793/500000000000 : ℝ) (63248644199/125000000000 : ℝ) (99816028967/200000000000 : ℝ) (249540072421/500000000000 : ℝ) (50253464921/100000000000 : ℝ) (502534649217/1000000000000 : ℝ) (502522775659/1000000000000 : ℝ) (502522775667/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4251/32768 : ℝ))) 3 (50253464921/100000000000 : ℝ) (502534649217/1000000000000 : ℝ) (502522775659/1000000000000 : ℝ) (502522775667/1000000000000 : ℝ) (251264356217/500000000000 : ℝ) (251264356221/500000000000 : ℝ) (502528712399/1000000000000 : ℝ) (502528712407/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4251/32768 : ℝ))) 4 (251264356217/500000000000 : ℝ) (251264356221/500000000000 : ℝ) (502528712399/1000000000000 : ℝ) (502528712407/1000000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4251/32768 : ℝ))) 5 (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4251/32768 : ℝ))) 6 (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4251/32768 : ℝ))) 7 (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4251/32768 : ℝ)) hmem 8 (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4251/32768 : ℝ))) hcmem 8 (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4251/32768 : ℝ)) (495970473019/500000000000 : ℝ) (991940946041/1000000000000 : ℝ) (15704022263/31250000000 : ℝ) (20101148497/40000000000 : ℝ) (397891758941/500000000000 : ℝ) (795783517899/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1484_exp_lower
  have heNumeric : (2054912850299/1000000000000 : ℝ)/4 ≤ Real.exp (-21313949525893/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054912850299/1000000000000 : ℝ)/4 ≤ Real.exp ((17003/131072 : ℝ)-(795783517899/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17003/131072 : ℝ) (4251/32768 : ℝ) (795783517899/1000000000000 : ℝ) (2054912850299/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1485; no trusted numerical premise.
theorem cover8_leaf1485_exp_radius : (498987449660058491/500000000000000000 : ℝ) ≤ Real.exp ((-17005/1048576 : ℝ)/8) ∧ Real.exp ((-17005/1048576 : ℝ)/8) ≤ (997974899320116983/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17005/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1485_exp_lower : (460057045350618653/500000000000000000 : ℝ) ≤ Real.exp ((-5328486719749/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328486719749/8000000000000 : ℝ)/8) ≤ (920114090701237307/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328486719749/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1485_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054913020273/1000000000000 : ℝ) ≤ 4*Real.exp (4251/32768 : ℝ)*Real.exp (-mu (radius 8 (17005/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054913020273/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17005/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1485_exp_radius
  have hrNumeric : (983913559573/1000000000000 : ℝ) ≤ Real.exp (-17005/1048576 : ℝ) ∧ Real.exp (-17005/1048576 : ℝ) ≤ (491956779787/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983913559573/1000000000000 : ℝ) ≤ (radius 8 (17005/131072 : ℝ)) ∧ (radius 8 (17005/131072 : ℝ)) ≤ (491956779787/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17005/131072 : ℝ)) (983913559573/1000000000000 : ℝ) (491956779787/500000000000 : ℝ) (178645199449/1000000000000 : ℝ) (5582662483/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17005/131072 : ℝ)) (983913559573/1000000000000 : ℝ) (491956779787/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17005/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983913559573/1000000000000 : ℝ) (491956779787/500000000000 : ℝ) (495978389893/500000000000 : ℝ) (991956779787/1000000000000 : ℝ) (991924170273/1000000000000 : ℝ) (39676966811/40000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17005/131072 : ℝ)) 1 (495978389893/500000000000 : ℝ) (991956779787/1000000000000 : ℝ) (991924170273/1000000000000 : ℝ) (39676966811/40000000000 : ℝ) (991940475029/1000000000000 : ℝ) (991940475031/1000000000000 : ℝ) (198388094979/200000000000 : ℝ) (991940474897/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17005/131072 : ℝ)) 2 (991940475029/1000000000000 : ℝ) (991940475031/1000000000000 : ℝ) (198388094979/200000000000 : ℝ) (991940474897/1000000000000 : ℝ) (495970237481/500000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17005/131072 : ℝ)) 3 (495970237481/500000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17005/131072 : ℝ)) 4 (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17005/131072 : ℝ)) 5 (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17005/131072 : ℝ)) 6 (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17005/131072 : ℝ)) 7 (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17005/131072 : ℝ))) (178645199449/1000000000000 : ℝ) (5582662483/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17005/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178645199449/1000000000000 : ℝ) (5582662483/31250000000 : ℝ) (147330649931/250000000000 : ℝ) (36832662483/62500000000 : ℝ) (42266440523/100000000000 : ℝ) (422664405239/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17005/131072 : ℝ))) 1 (147330649931/250000000000 : ℝ) (36832662483/62500000000 : ℝ) (42266440523/100000000000 : ℝ) (422664405239/1000000000000 : ℝ) (505993502477/1000000000000 : ℝ) (126498375621/250000000000 : ℝ) (249542424299/500000000000 : ℝ) (249542424303/500000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17005/131072 : ℝ))) 2 (505993502477/1000000000000 : ℝ) (126498375621/250000000000 : ℝ) (249542424299/500000000000 : ℝ) (249542424303/500000000000 : ℝ) (502539175537/1000000000000 : ℝ) (100507835109/200000000000 : ℝ) (502527303313/1000000000000 : ℝ) (502527303321/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17005/131072 : ℝ))) 3 (502539175537/1000000000000 : ℝ) (100507835109/200000000000 : ℝ) (502527303313/1000000000000 : ℝ) (502527303321/1000000000000 : ℝ) (20101329577/40000000000 : ℝ) (502533239433/1000000000000 : ℝ) (502533239389/1000000000000 : ℝ) (251266619699/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17005/131072 : ℝ))) 4 (20101329577/40000000000 : ℝ) (502533239433/1000000000000 : ℝ) (502533239389/1000000000000 : ℝ) (251266619699/500000000000 : ℝ) (502533239407/1000000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17005/131072 : ℝ))) 5 (502533239407/1000000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17005/131072 : ℝ))) 6 (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17005/131072 : ℝ))) 7 (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17005/131072 : ℝ)) hmem 8 (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17005/131072 : ℝ))) hcmem 8 (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17005/131072 : ℝ)) (991940474961/1000000000000 : ℝ) (247985118741/250000000000 : ℝ) (251266619703/500000000000 : ℝ) (62816654927/125000000000 : ℝ) (795791064559/1000000000000 : ℝ) (397895532289/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1485_exp_lower
  have heNumeric : (2054913020273/1000000000000 : ℝ)/4 ≤ Real.exp (-5328486719749/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054913020273/1000000000000 : ℝ)/4 ≤ Real.exp ((4251/32768 : ℝ)-(397895532289/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4251/32768 : ℝ) (17005/131072 : ℝ) (397895532289/500000000000 : ℝ) (2054913020273/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1486; no trusted numerical premise.
theorem cover8_leaf1486_exp_radius : (124746847544030667/125000000000000000 : ℝ) ≤ Real.exp ((-8503/524288 : ℝ)/8) ∧ Real.exp ((-8503/524288 : ℝ)/8) ≤ (997974780352245337/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8503/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1486_exp_lower : (115014262531165297/125000000000000000 : ℝ) ≤ Real.exp ((-21313944222467/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313944222467/32000000000000 : ℝ)/8) ≤ (920114100249322377/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313944222467/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1486_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (128432074429/62500000000 : ℝ) ≤ 4*Real.exp (17005/131072 : ℝ)*Real.exp (-mu (radius 8 (8503/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (128432074429/62500000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8503/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1486_exp_radius
  have hrNumeric : (24597815531/25000000000 : ℝ) ≤ Real.exp (-8503/524288 : ℝ) ∧ Real.exp (-8503/524288 : ℝ) ≤ (983912621241/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24597815531/25000000000 : ℝ) ≤ (radius 8 (8503/65536 : ℝ)) ∧ (radius 8 (8503/65536 : ℝ)) ≤ (983912621241/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8503/65536 : ℝ)) (24597815531/25000000000 : ℝ) (983912621241/1000000000000 : ℝ) (178650367373/1000000000000 : ℝ) (178650367379/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8503/65536 : ℝ)) (24597815531/25000000000 : ℝ) (983912621241/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8503/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24597815531/25000000000 : ℝ) (983912621241/1000000000000 : ℝ) (49597815531/50000000000 : ℝ) (991956310621/1000000000000 : ℝ) (991923697287/1000000000000 : ℝ) (123990462161/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8503/65536 : ℝ)) 1 (49597815531/50000000000 : ℝ) (991956310621/1000000000000 : ℝ) (991923697287/1000000000000 : ℝ) (123990462161/125000000000 : ℝ) (991940003953/1000000000000 : ℝ) (198388000791/200000000000 : ℝ) (991940003819/1000000000000 : ℝ) (991940003821/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8503/65536 : ℝ)) 2 (991940003953/1000000000000 : ℝ) (198388000791/200000000000 : ℝ) (991940003819/1000000000000 : ℝ) (991940003821/1000000000000 : ℝ) (495970001943/500000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8503/65536 : ℝ)) 3 (495970001943/500000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8503/65536 : ℝ)) 4 (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8503/65536 : ℝ)) 5 (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8503/65536 : ℝ)) 6 (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8503/65536 : ℝ)) 7 (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8503/65536 : ℝ))) (178650367373/1000000000000 : ℝ) (178650367379/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8503/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178650367373/1000000000000 : ℝ) (178650367379/1000000000000 : ℝ) (294662591843/500000000000 : ℝ) (58932518369/100000000000 : ℝ) (422670518693/1000000000000 : ℝ) (211335259351/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8503/65536 : ℝ))) 1 (294662591843/500000000000 : ℝ) (58932518369/100000000000 : ℝ) (422670518693/1000000000000 : ℝ) (211335259351/500000000000 : ℝ) (505997851189/1000000000000 : ℝ) (126499462799/250000000000 : ℝ) (62386194019/125000000000 : ℝ) (3119309701/6250000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8503/65536 : ℝ))) 2 (505997851189/1000000000000 : ℝ) (126499462799/250000000000 : ℝ) (62386194019/125000000000 : ℝ) (3119309701/6250000000 : ℝ) (50254370167/100000000000 : ℝ) (251271850839/500000000000 : ℝ) (125632957693/250000000000 : ℝ) (502531830781/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8503/65536 : ℝ))) 3 (50254370167/100000000000 : ℝ) (251271850839/500000000000 : ℝ) (125632957693/250000000000 : ℝ) (502531830781/1000000000000 : ℝ) (502537766221/1000000000000 : ℝ) (50253776623/100000000000 : ℝ) (100507553237/200000000000 : ℝ) (100507553239/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8503/65536 : ℝ))) 4 (502537766221/1000000000000 : ℝ) (50253776623/100000000000 : ℝ) (100507553237/200000000000 : ℝ) (100507553239/200000000000 : ℝ) (502537766203/1000000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8503/65536 : ℝ))) 5 (502537766203/1000000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8503/65536 : ℝ))) 6 (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8503/65536 : ℝ))) 7 (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8503/65536 : ℝ)) hmem 8 (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8503/65536 : ℝ))) hcmem 8 (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8503/65536 : ℝ)) (198388000777/200000000000 : ℝ) (61996250243/62500000000 : ℝ) (251268883101/500000000000 : ℝ) (502537766213/1000000000000 : ℝ) (159159722187/200000000000 : ℝ) (198949652739/250000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1486_exp_lower
  have heNumeric : (128432074429/62500000000 : ℝ)/4 ≤ Real.exp (-21313944222467/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (128432074429/62500000000 : ℝ)/4 ≤ Real.exp ((17005/131072 : ℝ)-(198949652739/250000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17005/131072 : ℝ) (8503/65536 : ℝ) (198949652739/250000000000 : ℝ) (128432074429/62500000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1487; no trusted numerical premise.
theorem cover8_leaf1487_exp_radius : (31186708168262121/31250000000000000 : ℝ) ≤ Real.exp ((-17007/1048576 : ℝ)/8) ∧ Real.exp ((-17007/1048576 : ℝ)/8) ≤ (997974661384387873/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17007/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1487_exp_lower : (920114109833176981/1000000000000000000 : ℝ) ≤ Real.exp ((-10656970777993/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656970777993/16000000000000 : ℝ)/8) ≤ (460057054916588491/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656970777993/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1487_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (410982672419/200000000000 : ℝ) ≤ 4*Real.exp (8503/65536 : ℝ)*Real.exp (-mu (radius 8 (17007/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (410982672419/200000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17007/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1487_exp_radius
  have hrNumeric : (983911682909/1000000000000 : ℝ) ≤ Real.exp (-17007/1048576 : ℝ) ∧ Real.exp (-17007/1048576 : ℝ) ≤ (98391168291/100000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983911682909/1000000000000 : ℝ) ≤ (radius 8 (17007/131072 : ℝ)) ∧ (radius 8 (17007/131072 : ℝ)) ≤ (98391168291/100000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17007/131072 : ℝ)) (983911682909/1000000000000 : ℝ) (98391168291/100000000000 : ℝ) (178655535131/1000000000000 : ℝ) (89327767569/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17007/131072 : ℝ)) (983911682909/1000000000000 : ℝ) (98391168291/100000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17007/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983911682909/1000000000000 : ℝ) (98391168291/100000000000 : ℝ) (495977920727/500000000000 : ℝ) (198391168291/200000000000 : ℝ) (991923224301/1000000000000 : ℝ) (991923224303/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17007/131072 : ℝ)) 1 (495977920727/500000000000 : ℝ) (198391168291/200000000000 : ℝ) (991923224301/1000000000000 : ℝ) (991923224303/1000000000000 : ℝ) (991939532877/1000000000000 : ℝ) (991939532879/1000000000000 : ℝ) (991939532743/1000000000000 : ℝ) (198387906549/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17007/131072 : ℝ)) 2 (991939532877/1000000000000 : ℝ) (991939532879/1000000000000 : ℝ) (991939532743/1000000000000 : ℝ) (198387906549/200000000000 : ℝ) (99193953281/100000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17007/131072 : ℝ)) 3 (99193953281/100000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17007/131072 : ℝ)) 4 (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17007/131072 : ℝ)) 5 (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17007/131072 : ℝ)) 6 (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17007/131072 : ℝ)) 7 (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17007/131072 : ℝ))) (178655535131/1000000000000 : ℝ) (89327767569/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17007/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178655535131/1000000000000 : ℝ) (89327767569/500000000000 : ℝ) (117865553513/200000000000 : ℝ) (589327767569/1000000000000 : ℝ) (6604322373/15625000000 : ℝ) (422676631881/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17007/131072 : ℝ))) 1 (117865553513/200000000000 : ℝ) (589327767569/1000000000000 : ℝ) (6604322373/15625000000 : ℝ) (422676631881/1000000000000 : ℝ) (253001099859/500000000000 : ℝ) (20240087989/40000000000 : ℝ) (499094255489/1000000000000 : ℝ) (499094255497/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17007/131072 : ℝ))) 2 (253001099859/500000000000 : ℝ) (20240087989/40000000000 : ℝ) (499094255489/1000000000000 : ℝ) (499094255497/1000000000000 : ℝ) (502548227603/1000000000000 : ℝ) (502548227611/1000000000000 : ℝ) (502536358031/1000000000000 : ℝ) (12563408951/25000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17007/131072 : ℝ))) 3 (502548227603/1000000000000 : ℝ) (502548227611/1000000000000 : ℝ) (502536358031/1000000000000 : ℝ) (12563408951/25000000000 : ℝ) (502542292817/1000000000000 : ℝ) (251271146413/500000000000 : ℝ) (502542292781/1000000000000 : ℝ) (502542292791/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17007/131072 : ℝ))) 4 (502542292817/1000000000000 : ℝ) (251271146413/500000000000 : ℝ) (502542292781/1000000000000 : ℝ) (502542292791/1000000000000 : ℝ) (502542292799/1000000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17007/131072 : ℝ))) 5 (502542292799/1000000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17007/131072 : ℝ))) 6 (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17007/131072 : ℝ))) 7 (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17007/131072 : ℝ)) hmem 8 (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17007/131072 : ℝ))) hcmem 8 (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17007/131072 : ℝ)) (991939532809/1000000000000 : ℝ) (247984883203/250000000000 : ℝ) (251271146399/500000000000 : ℝ) (502542292809/1000000000000 : ℝ) (397903078501/500000000000 : ℝ) (795806157023/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1487_exp_lower
  have heNumeric : (410982672419/200000000000 : ℝ)/4 ≤ Real.exp (-10656970777993/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (410982672419/200000000000 : ℝ)/4 ≤ Real.exp ((8503/65536 : ℝ)-(795806157023/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8503/65536 : ℝ) (17007/131072 : ℝ) (795806157023/1000000000000 : ℝ) (410982672419/200000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1488; no trusted numerical premise.
theorem cover8_leaf1488_exp_radius : (997974542416544589/1000000000000000000 : ℝ) ≤ Real.exp ((-1063/65536 : ℝ)/8) ∧ Real.exp ((-1063/65536 : ℝ)/8) ≤ (99797454241654459/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1063/65536 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1488_exp_lower : (460057059725365433/500000000000000000 : ℝ) ≤ Real.exp ((-21313938880129/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313938880129/32000000000000 : ℝ)/8) ≤ (920114119450730867/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313938880129/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1488_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256864191741/125000000000 : ℝ) ≤ 4*Real.exp (17007/131072 : ℝ)*Real.exp (-mu (radius 8 (1063/8192 : ℝ))) ∧ (20549/10000 : ℝ) < (256864191741/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (1063/8192 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1488_exp_radius
  have hrNumeric : (491955372289/500000000000 : ℝ) ≤ Real.exp (-1063/65536 : ℝ) ∧ Real.exp (-1063/65536 : ℝ) ≤ (983910744579/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491955372289/500000000000 : ℝ) ≤ (radius 8 (1063/8192 : ℝ)) ∧ (radius 8 (1063/8192 : ℝ)) ≤ (983910744579/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (1063/8192 : ℝ)) (491955372289/500000000000 : ℝ) (983910744579/1000000000000 : ℝ) (35732140547/200000000000 : ℝ) (89330351371/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (1063/8192 : ℝ)) (491955372289/500000000000 : ℝ) (983910744579/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (1063/8192 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491955372289/500000000000 : ℝ) (983910744579/1000000000000 : ℝ) (991955372289/1000000000000 : ℝ) (99195537229/100000000000 : ℝ) (198384550263/200000000000 : ℝ) (991922751317/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (1063/8192 : ℝ)) 1 (991955372289/1000000000000 : ℝ) (99195537229/100000000000 : ℝ) (198384550263/200000000000 : ℝ) (991922751317/1000000000000 : ℝ) (495969530901/500000000000 : ℝ) (247984765451/250000000000 : ℝ) (991939061667/1000000000000 : ℝ) (99193906167/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (1063/8192 : ℝ)) 2 (495969530901/500000000000 : ℝ) (247984765451/250000000000 : ℝ) (991939061667/1000000000000 : ℝ) (99193906167/100000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (1063/8192 : ℝ)) 3 (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (1063/8192 : ℝ)) 4 (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (1063/8192 : ℝ)) 5 (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (1063/8192 : ℝ)) 6 (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (1063/8192 : ℝ)) 7 (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (1063/8192 : ℝ))) (35732140547/200000000000 : ℝ) (89330351371/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (1063/8192 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (35732140547/200000000000 : ℝ) (89330351371/500000000000 : ℝ) (589330351367/1000000000000 : ℝ) (589330351371/1000000000000 : ℝ) (21134137239/50000000000 : ℝ) (422682744789/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (1063/8192 : ℝ))) 1 (589330351367/1000000000000 : ℝ) (589330351371/1000000000000 : ℝ) (21134137239/50000000000 : ℝ) (422682744789/1000000000000 : ℝ) (506006548073/1000000000000 : ℝ) (6325081851/12500000000 : ℝ) (249549479311/500000000000 : ℝ) (49909895863/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (1063/8192 : ℝ))) 2 (506006548073/1000000000000 : ℝ) (6325081851/12500000000 : ℝ) (249549479311/500000000000 : ℝ) (49909895863/100000000000 : ℝ) (502552753347/1000000000000 : ℝ) (100510550671/200000000000 : ℝ) (251270442551/500000000000 : ℝ) (50254088511/100000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (1063/8192 : ℝ))) 3 (502552753347/1000000000000 : ℝ) (100510550671/200000000000 : ℝ) (251270442551/500000000000 : ℝ) (50254088511/100000000000 : ℝ) (62818352403/125000000000 : ℝ) (502546819233/1000000000000 : ℝ) (502546819189/1000000000000 : ℝ) (251273409599/500000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (1063/8192 : ℝ))) 4 (62818352403/125000000000 : ℝ) (502546819233/1000000000000 : ℝ) (502546819189/1000000000000 : ℝ) (251273409599/500000000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (1063/8192 : ℝ))) 5 (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (1063/8192 : ℝ))) 6 (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (1063/8192 : ℝ))) 7 (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (1063/8192 : ℝ)) hmem 8 (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (1063/8192 : ℝ))) hcmem 8 (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (1063/8192 : ℝ)) (495969530867/500000000000 : ℝ) (991939061737/1000000000000 : ℝ) (251273409603/500000000000 : ℝ) (31409176201/62500000000 : ℝ) (397906851389/500000000000 : ℝ) (795813702797/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1488_exp_lower
  have heNumeric : (256864191741/125000000000 : ℝ)/4 ≤ Real.exp (-21313938880129/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256864191741/125000000000 : ℝ)/4 ≤ Real.exp ((17007/131072 : ℝ)-(795813702797/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17007/131072 : ℝ) (1063/8192 : ℝ) (795813702797/1000000000000 : ℝ) (256864191741/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1489; no trusted numerical premise.
theorem cover8_leaf1489_exp_radius : (997974423448715489/1000000000000000000 : ℝ) ≤ Real.exp ((-17009/1048576 : ℝ)/8) ∧ Real.exp ((-17009/1048576 : ℝ)/8) ≤ (99797442344871549/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17009/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1489_exp_lower : (920114129103019159/1000000000000000000 : ℝ) ≤ Real.exp ((-1332121012163/2000000000000 : ℝ)/8) ∧ Real.exp ((-1332121012163/2000000000000 : ℝ)/8) ≤ (23002853227575479/25000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-1332121012163/2000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1489_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027456853191/500000000000 : ℝ) ≤ 4*Real.exp (1063/8192 : ℝ)*Real.exp (-mu (radius 8 (17009/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027456853191/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17009/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1489_exp_radius
  have hrNumeric : (122988725781/125000000000 : ℝ) ≤ Real.exp (-17009/1048576 : ℝ) ∧ Real.exp (-17009/1048576 : ℝ) ≤ (983909806249/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (122988725781/125000000000 : ℝ) ≤ (radius 8 (17009/131072 : ℝ)) ∧ (radius 8 (17009/131072 : ℝ)) ≤ (983909806249/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17009/131072 : ℝ)) (122988725781/125000000000 : ℝ) (983909806249/1000000000000 : ℝ) (178665870179/1000000000000 : ℝ) (89332935093/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17009/131072 : ℝ)) (122988725781/125000000000 : ℝ) (983909806249/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17009/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (122988725781/125000000000 : ℝ) (983909806249/1000000000000 : ℝ) (247988725781/250000000000 : ℝ) (317425569/320000000 : ℝ) (99192227833/100000000000 : ℝ) (991922278331/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17009/131072 : ℝ)) 1 (247988725781/250000000000 : ℝ) (317425569/320000000 : ℝ) (99192227833/100000000000 : ℝ) (991922278331/1000000000000 : ℝ) (991938590727/1000000000000 : ℝ) (123992323841/125000000000 : ℝ) (7749520239/7812500000 : ℝ) (495969295297/500000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17009/131072 : ℝ)) 2 (991938590727/1000000000000 : ℝ) (123992323841/125000000000 : ℝ) (7749520239/7812500000 : ℝ) (495969295297/500000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17009/131072 : ℝ)) 3 (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17009/131072 : ℝ)) 4 (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17009/131072 : ℝ)) 5 (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17009/131072 : ℝ)) 6 (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17009/131072 : ℝ)) 7 (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17009/131072 : ℝ))) (178665870179/1000000000000 : ℝ) (89332935093/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17009/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178665870179/1000000000000 : ℝ) (89332935093/500000000000 : ℝ) (589332935089/1000000000000 : ℝ) (589332935093/1000000000000 : ℝ) (42268885741/100000000000 : ℝ) (422688857419/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17009/131072 : ℝ))) 1 (589332935089/1000000000000 : ℝ) (589332935093/1000000000000 : ℝ) (42268885741/100000000000 : ℝ) (422688857419/1000000000000 : ℝ) (506010896249/1000000000000 : ℝ) (3953210127/7812500000 : ℝ) (62387957693/125000000000 : ℝ) (31193978847/62500000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17009/131072 : ℝ))) 2 (506010896249/1000000000000 : ℝ) (3953210127/7812500000 : ℝ) (62387957693/125000000000 : ℝ) (31193978847/62500000000 : ℝ) (31409829931/62500000000 : ℝ) (62819659863/125000000000 : ℝ) (62818176497/125000000000 : ℝ) (100509082397/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17009/131072 : ℝ))) 3 (31409829931/62500000000 : ℝ) (62819659863/125000000000 : ℝ) (62818176497/125000000000 : ℝ) (100509082397/200000000000 : ℝ) (125637836359/250000000000 : ℝ) (100510269089/200000000000 : ℝ) (2512756727/5000000000 : ℝ) (50255134541/100000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17009/131072 : ℝ))) 4 (125637836359/250000000000 : ℝ) (100510269089/200000000000 : ℝ) (2512756727/5000000000 : ℝ) (50255134541/100000000000 : ℝ) (251275672709/500000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17009/131072 : ℝ))) 5 (251275672709/500000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17009/131072 : ℝ))) 6 (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17009/131072 : ℝ))) 7 (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17009/131072 : ℝ)) hmem 8 (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17009/131072 : ℝ))) hcmem 8 (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17009/131072 : ℝ)) (991938590659/1000000000000 : ℝ) (991938590661/1000000000000 : ℝ) (502551345417/1000000000000 : ℝ) (125637836357/250000000000 : ℝ) (795821248249/1000000000000 : ℝ) (795821248269/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1489_exp_lower
  have heNumeric : (1027456853191/500000000000 : ℝ)/4 ≤ Real.exp (-1332121012163/2000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027456853191/500000000000 : ℝ)/4 ≤ Real.exp ((1063/8192 : ℝ)-(795821248269/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (1063/8192 : ℝ) (17009/131072 : ℝ) (795821248269/1000000000000 : ℝ) (1027456853191/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1490; no trusted numerical premise.
theorem cover8_leaf1490_exp_radius : (997974304480900571/1000000000000000000 : ℝ) ≤ Real.exp ((-8505/524288 : ℝ)/8) ∧ Real.exp ((-8505/524288 : ℝ)/8) ≤ (249493576120225143/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8505/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1490_exp_lower : (14376783418592607/15625000000000000 : ℝ) ≤ Real.exp ((-4262786699891/6400000000000 : ℝ)/8) ∧ Real.exp ((-4262786699891/6400000000000 : ℝ)/8) ≤ (920114138789926849/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4262786699891/6400000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1490_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027456939727/500000000000 : ℝ) ≤ 4*Real.exp (17009/131072 : ℝ)*Real.exp (-mu (radius 8 (8505/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (1027456939727/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8505/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1490_exp_radius
  have hrNumeric : (983908867919/1000000000000 : ℝ) ≤ Real.exp (-8505/524288 : ℝ) ∧ Real.exp (-8505/524288 : ℝ) ≤ (12298860849/12500000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983908867919/1000000000000 : ℝ) ≤ (radius 8 (8505/65536 : ℝ)) ∧ (radius 8 (8505/65536 : ℝ)) ≤ (12298860849/12500000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8505/65536 : ℝ)) (983908867919/1000000000000 : ℝ) (12298860849/12500000000 : ℝ) (178671037463/1000000000000 : ℝ) (17867103747/100000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8505/65536 : ℝ)) (983908867919/1000000000000 : ℝ) (12298860849/12500000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8505/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983908867919/1000000000000 : ℝ) (12298860849/12500000000 : ℝ) (991954433959/1000000000000 : ℝ) (24798860849/25000000000 : ℝ) (198384361069/200000000000 : ℝ) (495960902673/500000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8505/65536 : ℝ)) 1 (991954433959/1000000000000 : ℝ) (24798860849/25000000000 : ℝ) (198384361069/200000000000 : ℝ) (495960902673/500000000000 : ℝ) (247984529913/250000000000 : ℝ) (991938119653/1000000000000 : ℝ) (991938119517/1000000000000 : ℝ) (991938119519/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8505/65536 : ℝ)) 2 (247984529913/250000000000 : ℝ) (991938119653/1000000000000 : ℝ) (991938119517/1000000000000 : ℝ) (991938119519/1000000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8505/65536 : ℝ)) 3 (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8505/65536 : ℝ)) 4 (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8505/65536 : ℝ)) 5 (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8505/65536 : ℝ)) 6 (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8505/65536 : ℝ)) 7 (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8505/65536 : ℝ))) (178671037463/1000000000000 : ℝ) (17867103747/100000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8505/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178671037463/1000000000000 : ℝ) (17867103747/100000000000 : ℝ) (589335518731/1000000000000 : ℝ) (117867103747/200000000000 : ℝ) (422694969763/1000000000000 : ℝ) (105673742443/250000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8505/65536 : ℝ))) 1 (589335518731/1000000000000 : ℝ) (117867103747/200000000000 : ℝ) (422694969763/1000000000000 : ℝ) (105673742443/250000000000 : ℝ) (506015244247/1000000000000 : ℝ) (253007622127/500000000000 : ℝ) (99821672851/200000000000 : ℝ) (499108364263/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8505/65536 : ℝ))) 2 (506015244247/1000000000000 : ℝ) (253007622127/500000000000 : ℝ) (99821672851/200000000000 : ℝ) (499108364263/1000000000000 : ℝ) (502561804251/1000000000000 : ℝ) (502561804259/1000000000000 : ℝ) (502549938657/1000000000000 : ℝ) (100509987733/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8505/65536 : ℝ))) 3 (502561804251/1000000000000 : ℝ) (502561804259/1000000000000 : ℝ) (502549938657/1000000000000 : ℝ) (100509987733/200000000000 : ℝ) (251277935727/500000000000 : ℝ) (251277935731/500000000000 : ℝ) (251277935709/500000000000 : ℝ) (502555871427/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8505/65536 : ℝ))) 4 (251277935727/500000000000 : ℝ) (251277935731/500000000000 : ℝ) (251277935709/500000000000 : ℝ) (502555871427/1000000000000 : ℝ) (125638967859/250000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8505/65536 : ℝ))) 5 (125638967859/250000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8505/65536 : ℝ))) 6 (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8505/65536 : ℝ))) 7 (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8505/65536 : ℝ)) hmem 8 (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8505/65536 : ℝ))) hcmem 8 (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8505/65536 : ℝ)) (30998066237/31250000000 : ℝ) (495969059793/500000000000 : ℝ) (100511174287/200000000000 : ℝ) (100511174289/200000000000 : ℝ) (795828793421/1000000000000 : ℝ) (4973929959/6250000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1490_exp_lower
  have heNumeric : (1027456939727/500000000000 : ℝ)/4 ≤ Real.exp (-4262786699891/6400000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027456939727/500000000000 : ℝ)/4 ≤ Real.exp ((17009/131072 : ℝ)-(4973929959/6250000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17009/131072 : ℝ) (8505/65536 : ℝ) (4973929959/6250000000 : ℝ) (1027456939727/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1491; no trusted numerical premise.
theorem cover8_leaf1491_exp_radius : (199594837102619967/200000000000000000 : ℝ) ≤ Real.exp ((-17011/1048576 : ℝ)/8) ∧ Real.exp ((-17011/1048576 : ℝ)/8) ≤ (249493546378274959/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17011/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1491_exp_lower : (460057074255726967/500000000000000000 : ℝ) ≤ Real.exp ((-2131393079467/3200000000000 : ℝ)/8) ∧ Real.exp ((-2131393079467/3200000000000 : ℝ)/8) ≤ (184022829702290787/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2131393079467/3200000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1491_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (256864256643/125000000000 : ℝ) ≤ 4*Real.exp (8505/65536 : ℝ)*Real.exp (-mu (radius 8 (17011/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (256864256643/125000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17011/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1491_exp_radius
  have hrNumeric : (983907929591/1000000000000 : ℝ) ≤ Real.exp (-17011/1048576 : ℝ) ∧ Real.exp (-17011/1048576 : ℝ) ≤ (122988491199/125000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983907929591/1000000000000 : ℝ) ≤ (radius 8 (17011/131072 : ℝ)) ∧ (radius 8 (17011/131072 : ℝ)) ≤ (122988491199/125000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17011/131072 : ℝ)) (983907929591/1000000000000 : ℝ) (122988491199/125000000000 : ℝ) (44669051147/250000000000 : ℝ) (89338102297/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17011/131072 : ℝ)) (983907929591/1000000000000 : ℝ) (122988491199/125000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17011/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983907929591/1000000000000 : ℝ) (122988491199/125000000000 : ℝ) (198390792959/200000000000 : ℝ) (247988491199/250000000000 : ℝ) (24798033309/25000000000 : ℝ) (991921332361/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17011/131072 : ℝ)) 1 (198390792959/200000000000 : ℝ) (247988491199/250000000000 : ℝ) (24798033309/25000000000 : ℝ) (991921332361/1000000000000 : ℝ) (991937648577/1000000000000 : ℝ) (991937648579/1000000000000 : ℝ) (991937648443/1000000000000 : ℝ) (198387529689/200000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17011/131072 : ℝ)) 2 (991937648577/1000000000000 : ℝ) (991937648579/1000000000000 : ℝ) (991937648443/1000000000000 : ℝ) (198387529689/200000000000 : ℝ) (99193764851/100000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17011/131072 : ℝ)) 3 (99193764851/100000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17011/131072 : ℝ)) 4 (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17011/131072 : ℝ)) 5 (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17011/131072 : ℝ)) 6 (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17011/131072 : ℝ)) 7 (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17011/131072 : ℝ))) (44669051147/250000000000 : ℝ) (89338102297/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17011/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44669051147/250000000000 : ℝ) (89338102297/500000000000 : ℝ) (294669051147/500000000000 : ℝ) (589338102297/1000000000000 : ℝ) (422701081839/1000000000000 : ℝ) (422701081847/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17011/131072 : ℝ))) 1 (294669051147/500000000000 : ℝ) (589338102297/1000000000000 : ℝ) (422701081839/1000000000000 : ℝ) (422701081847/1000000000000 : ℝ) (253009796033/500000000000 : ℝ) (63252449009/125000000000 : ℝ) (249556533379/500000000000 : ℝ) (99822613353/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17011/131072 : ℝ))) 2 (253009796033/500000000000 : ℝ) (63252449009/125000000000 : ℝ) (249556533379/500000000000 : ℝ) (99822613353/200000000000 : ℝ) (125641582353/250000000000 : ℝ) (502566329419/1000000000000 : ℝ) (502554465143/1000000000000 : ℝ) (502554465151/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17011/131072 : ℝ))) 3 (125641582353/250000000000 : ℝ) (502566329419/1000000000000 : ℝ) (502554465143/1000000000000 : ℝ) (502554465151/1000000000000 : ℝ) (502560397277/1000000000000 : ℝ) (100512079457/200000000000 : ℝ) (251280198621/500000000000 : ℝ) (2010241589/4000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17011/131072 : ℝ))) 4 (502560397277/1000000000000 : ℝ) (100512079457/200000000000 : ℝ) (251280198621/500000000000 : ℝ) (2010241589/4000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17011/131072 : ℝ))) 5 (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17011/131072 : ℝ))) 6 (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17011/131072 : ℝ))) 7 (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17011/131072 : ℝ)) hmem 8 (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17011/131072 : ℝ))) hcmem 8 (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17011/131072 : ℝ)) (991937648509/1000000000000 : ℝ) (7749512879/7812500000 : ℝ) (502560397259/1000000000000 : ℝ) (125640099317/250000000000 : ℝ) (795836338293/1000000000000 : ℝ) (79583633831/100000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1491_exp_lower
  have heNumeric : (256864256643/125000000000 : ℝ)/4 ≤ Real.exp (-2131393079467/3200000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (256864256643/125000000000 : ℝ)/4 ≤ Real.exp ((8505/65536 : ℝ)-(79583633831/100000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8505/65536 : ℝ) (17011/131072 : ℝ) (79583633831/100000000000 : ℝ) (256864256643/125000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1492; no trusted numerical premise.
theorem cover8_leaf1492_exp_radius : (997974066545313281/1000000000000000000 : ℝ) ≤ Real.exp ((-4253/262144 : ℝ)/8) ∧ Real.exp ((-4253/262144 : ℝ)/8) ≤ (498987033272656641/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-4253/262144 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1492_exp_lower : (57507134891667519/62500000000000000 : ℝ) ≤ Real.exp ((-21313928080509/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313928080509/32000000000000 : ℝ)/8) ≤ (184022831653336061/200000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313928080509/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1492_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054914227437/1000000000000 : ℝ) ≤ 4*Real.exp (17011/131072 : ℝ)*Real.exp (-mu (radius 8 (4253/32768 : ℝ))) ∧ (20549/10000 : ℝ) < (2054914227437/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (4253/32768 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1492_exp_radius
  have hrNumeric : (983906991263/1000000000000 : ℝ) ≤ Real.exp (-4253/262144 : ℝ) ∧ Real.exp (-4253/262144 : ℝ) ≤ (30747093477/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983906991263/1000000000000 : ℝ) ≤ (radius 8 (4253/32768 : ℝ)) ∧ (radius 8 (4253/32768 : ℝ)) ≤ (30747093477/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (4253/32768 : ℝ)) (983906991263/1000000000000 : ℝ) (30747093477/31250000000 : ℝ) (178681371557/1000000000000 : ℝ) (44670342891/250000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (4253/32768 : ℝ)) (983906991263/1000000000000 : ℝ) (30747093477/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (4253/32768 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983906991263/1000000000000 : ℝ) (30747093477/31250000000 : ℝ) (991953495631/1000000000000 : ℝ) (61997093477/62500000000 : ℝ) (495960429687/500000000000 : ℝ) (61995053711/62500000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (4253/32768 : ℝ)) 1 (991953495631/1000000000000 : ℝ) (61997093477/62500000000 : ℝ) (495960429687/500000000000 : ℝ) (61995053711/62500000000 : ℝ) (495968588751/500000000000 : ℝ) (30998036797/31250000000 : ℝ) (123992147171/125000000000 : ℝ) (99193717737/100000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (4253/32768 : ℝ)) 2 (495968588751/500000000000 : ℝ) (30998036797/31250000000 : ℝ) (123992147171/125000000000 : ℝ) (99193717737/100000000000 : ℝ) (198387435487/200000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (4253/32768 : ℝ)) 3 (198387435487/200000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (4253/32768 : ℝ)) 4 (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (4253/32768 : ℝ)) 5 (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (4253/32768 : ℝ)) 6 (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (4253/32768 : ℝ)) 7 (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (4253/32768 : ℝ))) (178681371557/1000000000000 : ℝ) (44670342891/250000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (4253/32768 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178681371557/1000000000000 : ℝ) (44670342891/250000000000 : ℝ) (294670342889/500000000000 : ℝ) (294670342891/500000000000 : ℝ) (211353596821/500000000000 : ℝ) (422707193651/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (4253/32768 : ℝ))) 1 (294670342889/500000000000 : ℝ) (294670342891/500000000000 : ℝ) (211353596821/500000000000 : ℝ) (422707193651/1000000000000 : ℝ) (50602393971/100000000000 : ℝ) (506023939717/1000000000000 : ℝ) (124779442263/250000000000 : ℝ) (24955888453/50000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (4253/32768 : ℝ))) 2 (50602393971/100000000000 : ℝ) (506023939717/1000000000000 : ℝ) (124779442263/250000000000 : ℝ) (24955888453/50000000000 : ℝ) (502570854381/1000000000000 : ℝ) (502570854389/1000000000000 : ℝ) (502558991437/1000000000000 : ℝ) (251279495723/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (4253/32768 : ℝ))) 3 (502570854381/1000000000000 : ℝ) (502570854389/1000000000000 : ℝ) (502558991437/1000000000000 : ℝ) (251279495723/500000000000 : ℝ) (502564922909/1000000000000 : ℝ) (251282461459/500000000000 : ℝ) (502564922873/1000000000000 : ℝ) (502564922883/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (4253/32768 : ℝ))) 4 (502564922909/1000000000000 : ℝ) (251282461459/500000000000 : ℝ) (502564922873/1000000000000 : ℝ) (502564922883/1000000000000 : ℝ) (502564922891/1000000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (4253/32768 : ℝ))) 5 (502564922891/1000000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (4253/32768 : ℝ))) 6 (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (4253/32768 : ℝ))) 7 (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (4253/32768 : ℝ)) hmem 8 (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (4253/32768 : ℝ))) hcmem 8 (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (4253/32768 : ℝ)) (495968588717/500000000000 : ℝ) (991937177437/1000000000000 : ℝ) (50256492289/100000000000 : ℝ) (502564922901/1000000000000 : ℝ) (397921941433/500000000000 : ℝ) (795843882887/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1492_exp_lower
  have heNumeric : (2054914227437/1000000000000 : ℝ)/4 ≤ Real.exp (-21313928080509/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054914227437/1000000000000 : ℝ)/4 ≤ Real.exp ((17011/131072 : ℝ)-(795843882887/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17011/131072 : ℝ) (4253/32768 : ℝ) (795843882887/1000000000000 : ℝ) (2054914227437/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1493; no trusted numerical premise.
theorem cover8_leaf1493_exp_radius : (997973947577540909/1000000000000000000 : ℝ) ≤ Real.exp ((-17013/1048576 : ℝ)/8) ∧ Real.exp ((-17013/1048576 : ℝ)/8) ≤ (99797394757754091/100000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17013/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1493_exp_lower : (115014271007209527/125000000000000000 : ℝ) ≤ Real.exp ((-5328481339099/8000000000000 : ℝ)/8) ∧ Real.exp ((-5328481339099/8000000000000 : ℝ)/8) ≤ (920114168057676217/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-5328481339099/8000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1493_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054914402369/1000000000000 : ℝ) ≤ 4*Real.exp (4253/32768 : ℝ)*Real.exp (-mu (radius 8 (17013/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054914402369/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17013/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1493_exp_radius
  have hrNumeric : (983906052937/1000000000000 : ℝ) ≤ Real.exp (-17013/1048576 : ℝ) ∧ Real.exp (-17013/1048576 : ℝ) ≤ (491953026469/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983906052937/1000000000000 : ℝ) ≤ (radius 8 (17013/131072 : ℝ)) ∧ (radius 8 (17013/131072 : ℝ)) ≤ (491953026469/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17013/131072 : ℝ)) (983906052937/1000000000000 : ℝ) (491953026469/500000000000 : ℝ) (89343269181/500000000000 : ℝ) (1395988581/7812500000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17013/131072 : ℝ)) (983906052937/1000000000000 : ℝ) (491953026469/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17013/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983906052937/1000000000000 : ℝ) (491953026469/500000000000 : ℝ) (247988256617/250000000000 : ℝ) (991953026469/1000000000000 : ℝ) (99192038639/100000000000 : ℝ) (991920386391/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17013/131072 : ℝ)) 1 (247988256617/250000000000 : ℝ) (991953026469/1000000000000 : ℝ) (99192038639/100000000000 : ℝ) (991920386391/1000000000000 : ℝ) (991936706429/1000000000000 : ℝ) (99193670643/100000000000 : ℝ) (495968353147/500000000000 : ℝ) (123992088287/125000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17013/131072 : ℝ)) 2 (991936706429/1000000000000 : ℝ) (99193670643/100000000000 : ℝ) (495968353147/500000000000 : ℝ) (123992088287/125000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17013/131072 : ℝ)) 3 (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17013/131072 : ℝ)) 4 (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17013/131072 : ℝ)) 5 (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17013/131072 : ℝ)) 6 (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17013/131072 : ℝ)) 7 (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17013/131072 : ℝ))) (89343269181/500000000000 : ℝ) (1395988581/7812500000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17013/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (89343269181/500000000000 : ℝ) (1395988581/7812500000 : ℝ) (589343269181/1000000000000 : ℝ) (9208488581/15625000000 : ℝ) (422713305163/1000000000000 : ℝ) (422713305171/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17013/131072 : ℝ))) 1 (589343269181/1000000000000 : ℝ) (9208488581/15625000000 : ℝ) (422713305163/1000000000000 : ℝ) (422713305171/1000000000000 : ℝ) (126507071793/250000000000 : ℝ) (253014143589/500000000000 : ℝ) (249561235567/500000000000 : ℝ) (499122471141/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17013/131072 : ℝ))) 2 (126507071793/250000000000 : ℝ) (253014143589/500000000000 : ℝ) (249561235567/500000000000 : ℝ) (499122471141/1000000000000 : ℝ) (502575379153/1000000000000 : ℝ) (12564384479/25000000000 : ℝ) (251281758767/500000000000 : ℝ) (251281758771/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17013/131072 : ℝ))) 3 (502575379153/1000000000000 : ℝ) (12564384479/25000000000 : ℝ) (251281758767/500000000000 : ℝ) (251281758771/500000000000 : ℝ) (502569448343/1000000000000 : ℝ) (502569448351/1000000000000 : ℝ) (125642362077/250000000000 : ℝ) (502569448317/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17013/131072 : ℝ))) 4 (502569448343/1000000000000 : ℝ) (502569448351/1000000000000 : ℝ) (125642362077/250000000000 : ℝ) (502569448317/1000000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17013/131072 : ℝ))) 5 (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17013/131072 : ℝ))) 6 (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17013/131072 : ℝ))) 7 (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17013/131072 : ℝ)) hmem 8 (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17013/131072 : ℝ))) hcmem 8 (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17013/131072 : ℝ)) (991936706361/1000000000000 : ℝ) (991936706363/1000000000000 : ℝ) (20102777933/40000000000 : ℝ) (251284724167/500000000000 : ℝ) (12435178549/15625000000 : ℝ) (795851427153/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1493_exp_lower
  have heNumeric : (2054914402369/1000000000000 : ℝ)/4 ≤ Real.exp (-5328481339099/8000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054914402369/1000000000000 : ℝ)/4 ≤ Real.exp ((4253/32768 : ℝ)-(795851427153/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (4253/32768 : ℝ) (17013/131072 : ℝ) (795851427153/1000000000000 : ℝ) (2054914402369/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1494; no trusted numerical premise.
theorem cover8_leaf1494_exp_radius : (997973828609782719/1000000000000000000 : ℝ) ≤ Real.exp ((-8507/524288 : ℝ)/8) ∧ Real.exp ((-8507/524288 : ℝ)/8) ≤ (3118668214405571/3125000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8507/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1494_exp_lower : (92011417788202637/100000000000000000 : ℝ) ≤ Real.exp ((-21313922623003/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313922623003/32000000000000 : ℝ)/8) ≤ (920114177882026371/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313922623003/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1494_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054914577897/1000000000000 : ℝ) ≤ 4*Real.exp (17013/131072 : ℝ)*Real.exp (-mu (radius 8 (8507/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054914577897/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8507/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1494_exp_radius
  have hrNumeric : (983905114611/1000000000000 : ℝ) ≤ Real.exp (-8507/524288 : ℝ) ∧ Real.exp (-8507/524288 : ℝ) ≤ (245976278653/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983905114611/1000000000000 : ℝ) ≤ (radius 8 (8507/65536 : ℝ)) ∧ (radius 8 (8507/65536 : ℝ)) ≤ (245976278653/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8507/65536 : ℝ)) (983905114611/1000000000000 : ℝ) (245976278653/250000000000 : ℝ) (44672926253/250000000000 : ℝ) (178691705019/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8507/65536 : ℝ)) (983905114611/1000000000000 : ℝ) (245976278653/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8507/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983905114611/1000000000000 : ℝ) (245976278653/250000000000 : ℝ) (198390511461/200000000000 : ℝ) (495976278653/500000000000 : ℝ) (198383982681/200000000000 : ℝ) (991919913407/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8507/65536 : ℝ)) 1 (198390511461/200000000000 : ℝ) (495976278653/500000000000 : ℝ) (198383982681/200000000000 : ℝ) (991919913407/1000000000000 : ℝ) (198387247071/200000000000 : ℝ) (991936235357/1000000000000 : ℝ) (49596811761/50000000000 : ℝ) (991936235223/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8507/65536 : ℝ)) 2 (198387247071/200000000000 : ℝ) (991936235357/1000000000000 : ℝ) (49596811761/50000000000 : ℝ) (991936235223/1000000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8507/65536 : ℝ)) 3 (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8507/65536 : ℝ)) 4 (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8507/65536 : ℝ)) 5 (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8507/65536 : ℝ)) 6 (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8507/65536 : ℝ)) 7 (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8507/65536 : ℝ))) (44672926253/250000000000 : ℝ) (178691705019/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8507/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44672926253/250000000000 : ℝ) (178691705019/1000000000000 : ℝ) (294672926253/500000000000 : ℝ) (58934585251/100000000000 : ℝ) (105679854103/250000000000 : ℝ) (422719416421/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8507/65536 : ℝ))) 1 (294672926253/500000000000 : ℝ) (58934585251/100000000000 : ℝ) (105679854103/250000000000 : ℝ) (422719416421/1000000000000 : ℝ) (506032634459/1000000000000 : ℝ) (253016317233/500000000000 : ℝ) (499127173009/1000000000000 : ℝ) (499127173017/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8507/65536 : ℝ))) 2 (506032634459/1000000000000 : ℝ) (253016317233/500000000000 : ℝ) (499127173009/1000000000000 : ℝ) (499127173017/1000000000000 : ℝ) (251289951867/500000000000 : ℝ) (251289951871/500000000000 : ℝ) (6282100543/12500000000 : ℝ) (502568043449/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8507/65536 : ℝ))) 3 (251289951867/500000000000 : ℝ) (251289951871/500000000000 : ℝ) (6282100543/12500000000 : ℝ) (502568043449/1000000000000 : ℝ) (502573973587/1000000000000 : ℝ) (125643493399/250000000000 : ℝ) (31410873347/62500000000 : ℝ) (502573973561/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8507/65536 : ℝ))) 4 (502573973587/1000000000000 : ℝ) (125643493399/250000000000 : ℝ) (31410873347/62500000000 : ℝ) (502573973561/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8507/65536 : ℝ))) 5 (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8507/65536 : ℝ))) 6 (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8507/65536 : ℝ))) 7 (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8507/65536 : ℝ)) hmem 8 (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8507/65536 : ℝ))) hcmem 8 (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8507/65536 : ℝ)) (991936235287/1000000000000 : ℝ) (99193623529/100000000000 : ℝ) (502573973569/1000000000000 : ℝ) (502573973579/1000000000000 : ℝ) (79585897111/100000000000 : ℝ) (795858971129/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1494_exp_lower
  have heNumeric : (2054914577897/1000000000000 : ℝ)/4 ≤ Real.exp (-21313922623003/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054914577897/1000000000000 : ℝ)/4 ≤ Real.exp ((17013/131072 : ℝ)-(795858971129/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17013/131072 : ℝ) (8507/65536 : ℝ) (795858971129/1000000000000 : ℝ) (2054914577897/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1495; no trusted numerical premise.
theorem cover8_leaf1495_exp_radius : (997973709642038711/1000000000000000000 : ℝ) ≤ Real.exp ((-17015/1048576 : ℝ)/8) ∧ Real.exp ((-17015/1048576 : ℝ)/8) ≤ (124746713705254839/125000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17015/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1495_exp_lower : (920114187742261083/1000000000000000000 : ℝ) ≤ Real.exp ((-10656959939813/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656959939813/16000000000000 : ℝ)/8) ≤ (230028546935565271/250000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656959939813/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1495_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (1027457377033/500000000000 : ℝ) ≤ 4*Real.exp (8507/65536 : ℝ)*Real.exp (-mu (radius 8 (17015/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (1027457377033/500000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17015/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1495_exp_radius
  have hrNumeric : (983904176287/1000000000000 : ℝ) ≤ Real.exp (-17015/1048576 : ℝ) ∧ Real.exp (-17015/1048576 : ℝ) ≤ (30747005509/31250000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983904176287/1000000000000 : ℝ) ≤ (radius 8 (17015/131072 : ℝ)) ∧ (radius 8 (17015/131072 : ℝ)) ≤ (30747005509/31250000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17015/131072 : ℝ)) (983904176287/1000000000000 : ℝ) (30747005509/31250000000 : ℝ) (178696871497/1000000000000 : ℝ) (11168554469/62500000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17015/131072 : ℝ)) (983904176287/1000000000000 : ℝ) (30747005509/31250000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17015/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983904176287/1000000000000 : ℝ) (30747005509/31250000000 : ℝ) (991952088143/1000000000000 : ℝ) (61997005509/62500000000 : ℝ) (991919440421/1000000000000 : ℝ) (991919440423/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17015/131072 : ℝ)) 1 (991952088143/1000000000000 : ℝ) (61997005509/62500000000 : ℝ) (991919440421/1000000000000 : ℝ) (991919440423/1000000000000 : ℝ) (495967882141/500000000000 : ℝ) (247983941071/250000000000 : ℝ) (991935764147/1000000000000 : ℝ) (19838715283/20000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17015/131072 : ℝ)) 2 (495967882141/500000000000 : ℝ) (247983941071/250000000000 : ℝ) (991935764147/1000000000000 : ℝ) (19838715283/20000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17015/131072 : ℝ)) 3 (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17015/131072 : ℝ)) 4 (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17015/131072 : ℝ)) 5 (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17015/131072 : ℝ)) 6 (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17015/131072 : ℝ)) 7 (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17015/131072 : ℝ))) (178696871497/1000000000000 : ℝ) (11168554469/62500000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17015/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178696871497/1000000000000 : ℝ) (11168554469/62500000000 : ℝ) (147337108937/250000000000 : ℝ) (73668554469/125000000000 : ℝ) (422725527377/1000000000000 : ℝ) (422725527387/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17015/131072 : ℝ))) 1 (147337108937/250000000000 : ℝ) (73668554469/125000000000 : ℝ) (422725527377/1000000000000 : ℝ) (422725527387/1000000000000 : ℝ) (253018490781/500000000000 : ℝ) (50603698157/100000000000 : ℝ) (124782968667/250000000000 : ℝ) (499131874677/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17015/131072 : ℝ))) 2 (253018490781/500000000000 : ℝ) (50603698157/100000000000 : ℝ) (124782968667/250000000000 : ℝ) (499131874677/1000000000000 : ℝ) (100516885623/200000000000 : ℝ) (125646107031/250000000000 : ℝ) (251286284573/500000000000 : ℝ) (100514513831/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17015/131072 : ℝ))) 3 (100516885623/200000000000 : ℝ) (125646107031/250000000000 : ℝ) (251286284573/500000000000 : ℝ) (100514513831/200000000000 : ℝ) (50257849863/100000000000 : ℝ) (6282231233/12500000000 : ℝ) (100515699719/200000000000 : ℝ) (100515699721/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17015/131072 : ℝ))) 4 (50257849863/100000000000 : ℝ) (6282231233/12500000000 : ℝ) (100515699719/200000000000 : ℝ) (100515699721/200000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17015/131072 : ℝ))) 5 (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17015/131072 : ℝ))) 6 (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17015/131072 : ℝ))) 7 (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17015/131072 : ℝ)) hmem 8 (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17015/131072 : ℝ))) hcmem 8 (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17015/131072 : ℝ)) (495967882107/500000000000 : ℝ) (991935764217/1000000000000 : ℝ) (125644624653/250000000000 : ℝ) (502578498623/1000000000000 : ℝ) (198966628693/250000000000 : ℝ) (795866514793/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1495_exp_lower
  have heNumeric : (1027457377033/500000000000 : ℝ)/4 ≤ Real.exp (-10656959939813/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (1027457377033/500000000000 : ℝ)/4 ≤ Real.exp ((8507/65536 : ℝ)-(795866514793/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8507/65536 : ℝ) (17015/131072 : ℝ) (795866514793/1000000000000 : ℝ) (1027457377033/500000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1496; no trusted numerical premise.
theorem cover8_leaf1496_exp_radius : (498986795337154443/500000000000000000 : ℝ) ≤ Real.exp ((-2127/131072 : ℝ)/8) ∧ Real.exp ((-2127/131072 : ℝ)/8) ≤ (997973590674308887/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2127/131072 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1496_exp_lower : (920114197636425113/1000000000000000000 : ℝ) ≤ Real.exp ((-21313917126809/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313917126809/32000000000000 : ℝ)/8) ≤ (460057098818212557/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313917126809/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1496_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054914930841/1000000000000 : ℝ) ≤ 4*Real.exp (17015/131072 : ℝ)*Real.exp (-mu (radius 8 (2127/16384 : ℝ))) ∧ (20549/10000 : ℝ) < (2054914930841/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (2127/16384 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1496_exp_radius
  have hrNumeric : (983903237963/1000000000000 : ℝ) ≤ Real.exp (-2127/131072 : ℝ) ∧ Real.exp (-2127/131072 : ℝ) ≤ (245975809491/250000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983903237963/1000000000000 : ℝ) ≤ (radius 8 (2127/16384 : ℝ)) ∧ (radius 8 (2127/16384 : ℝ)) ≤ (245975809491/250000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (2127/16384 : ℝ)) (983903237963/1000000000000 : ℝ) (245975809491/250000000000 : ℝ) (44675509457/250000000000 : ℝ) (89351018917/500000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (2127/16384 : ℝ)) (983903237963/1000000000000 : ℝ) (245975809491/250000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (2127/16384 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983903237963/1000000000000 : ℝ) (245975809491/250000000000 : ℝ) (991951618981/1000000000000 : ℝ) (495975809491/500000000000 : ℝ) (991918967437/1000000000000 : ℝ) (991918967439/1000000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (2127/16384 : ℝ)) 1 (991951618981/1000000000000 : ℝ) (495975809491/500000000000 : ℝ) (991918967437/1000000000000 : ℝ) (991918967439/1000000000000 : ℝ) (991935293209/1000000000000 : ℝ) (991935293211/1000000000000 : ℝ) (495967646537/500000000000 : ℝ) (991935293077/1000000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (2127/16384 : ℝ)) 2 (991935293209/1000000000000 : ℝ) (991935293211/1000000000000 : ℝ) (495967646537/500000000000 : ℝ) (991935293077/1000000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (2127/16384 : ℝ)) 3 (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (2127/16384 : ℝ)) 4 (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (2127/16384 : ℝ)) 5 (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (2127/16384 : ℝ)) 6 (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (2127/16384 : ℝ)) 7 (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (2127/16384 : ℝ))) (44675509457/250000000000 : ℝ) (89351018917/500000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (2127/16384 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (44675509457/250000000000 : ℝ) (89351018917/500000000000 : ℝ) (294675509457/500000000000 : ℝ) (589351018917/1000000000000 : ℝ) (422731638073/1000000000000 : ℝ) (422731638081/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (2127/16384 : ℝ))) 1 (294675509457/500000000000 : ℝ) (589351018917/1000000000000 : ℝ) (422731638073/1000000000000 : ℝ) (422731638081/1000000000000 : ℝ) (506041328493/1000000000000 : ℝ) (506041328499/1000000000000 : ℝ) (124784144031/250000000000 : ℝ) (499136576131/1000000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (2127/16384 : ℝ))) 2 (506041328493/1000000000000 : ℝ) (506041328499/1000000000000 : ℝ) (124784144031/250000000000 : ℝ) (499136576131/1000000000000 : ℝ) (125647238077/250000000000 : ℝ) (100517790463/200000000000 : ℝ) (62822136833/125000000000 : ℝ) (502577094671/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (2127/16384 : ℝ))) 3 (125647238077/250000000000 : ℝ) (100517790463/200000000000 : ℝ) (62822136833/125000000000 : ℝ) (502577094671/1000000000000 : ℝ) (251291511743/500000000000 : ℝ) (502583023493/1000000000000 : ℝ) (502583023451/1000000000000 : ℝ) (502583023459/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (2127/16384 : ℝ))) 4 (251291511743/500000000000 : ℝ) (502583023493/1000000000000 : ℝ) (502583023451/1000000000000 : ℝ) (502583023459/1000000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (2127/16384 : ℝ))) 5 (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (2127/16384 : ℝ))) 6 (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (2127/16384 : ℝ))) 7 (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (2127/16384 : ℝ)) hmem 8 (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (2127/16384 : ℝ))) hcmem 8 (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (2127/16384 : ℝ)) (991935293141/1000000000000 : ℝ) (123991911643/125000000000 : ℝ) (125645755867/250000000000 : ℝ) (125645755869/250000000000 : ℝ) (397937029073/500000000000 : ℝ) (397937029081/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1496_exp_lower
  have heNumeric : (2054914930841/1000000000000 : ℝ)/4 ≤ Real.exp (-21313917126809/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054914930841/1000000000000 : ℝ)/4 ≤ Real.exp ((17015/131072 : ℝ)-(397937029081/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17015/131072 : ℝ) (2127/16384 : ℝ) (397937029081/500000000000 : ℝ) (2054914930841/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1497; no trusted numerical premise.
theorem cover8_leaf1497_exp_radius : (498986735853296621/500000000000000000 : ℝ) ≤ Real.exp ((-17017/1048576 : ℝ)/8) ∧ Real.exp ((-17017/1048576 : ℝ)/8) ≤ (997973471706593243/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17017/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1497_exp_lower : (920114207564863503/1000000000000000000 : ℝ) ≤ Real.exp ((-2664239295557/4000000000000 : ℝ)/8) ∧ Real.exp ((-2664239295557/4000000000000 : ℝ)/8) ≤ (57507137972803969/62500000000000000 : ℝ) := by
  have h := exp_small_bounds ((-2664239295557/4000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1497_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (513728777057/250000000000 : ℝ) ≤ 4*Real.exp (2127/16384 : ℝ)*Real.exp (-mu (radius 8 (17017/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (513728777057/250000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17017/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1497_exp_radius
  have hrNumeric : (24597557491/25000000000 : ℝ) ≤ Real.exp (-17017/1048576 : ℝ) ∧ Real.exp (-17017/1048576 : ℝ) ≤ (983902299641/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (24597557491/25000000000 : ℝ) ≤ (radius 8 (17017/131072 : ℝ)) ∧ (radius 8 (17017/131072 : ℝ)) ≤ (983902299641/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17017/131072 : ℝ)) (24597557491/25000000000 : ℝ) (983902299641/1000000000000 : ℝ) (178707203999/1000000000000 : ℝ) (35741440801/200000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17017/131072 : ℝ)) (24597557491/25000000000 : ℝ) (983902299641/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17017/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (24597557491/25000000000 : ℝ) (983902299641/1000000000000 : ℝ) (49597557491/50000000000 : ℝ) (991951149821/1000000000000 : ℝ) (495959247227/500000000000 : ℝ) (198383698891/200000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17017/131072 : ℝ)) 1 (49597557491/50000000000 : ℝ) (991951149821/1000000000000 : ℝ) (495959247227/500000000000 : ℝ) (198383698891/200000000000 : ℝ) (991934822137/1000000000000 : ℝ) (495967411069/500000000000 : ℝ) (495967411001/500000000000 : ℝ) (247983705501/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17017/131072 : ℝ)) 2 (991934822137/1000000000000 : ℝ) (495967411069/500000000000 : ℝ) (495967411001/500000000000 : ℝ) (247983705501/250000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17017/131072 : ℝ)) 3 (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17017/131072 : ℝ)) 4 (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17017/131072 : ℝ)) 5 (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17017/131072 : ℝ)) 6 (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17017/131072 : ℝ)) 7 (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17017/131072 : ℝ))) (178707203999/1000000000000 : ℝ) (35741440801/200000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17017/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178707203999/1000000000000 : ℝ) (35741440801/200000000000 : ℝ) (589353601999/1000000000000 : ℝ) (589353602003/1000000000000 : ℝ) (42273774849/100000000000 : ℝ) (211368874249/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17017/131072 : ℝ))) 1 (589353601999/1000000000000 : ℝ) (589353602003/1000000000000 : ℝ) (42273774849/100000000000 : ℝ) (211368874249/500000000000 : ℝ) (126511418811/250000000000 : ℝ) (506045675251/1000000000000 : ℝ) (62392659671/125000000000 : ℝ) (7799082459/15625000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17017/131072 : ℝ))) 2 (126511418811/250000000000 : ℝ) (506045675251/1000000000000 : ℝ) (62392659671/125000000000 : ℝ) (7799082459/15625000000 : ℝ) (251296738153/500000000000 : ℝ) (251296738157/500000000000 : ℝ) (251290809993/500000000000 : ℝ) (251290809997/500000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17017/131072 : ℝ))) 3 (251296738153/500000000000 : ℝ) (251296738157/500000000000 : ℝ) (251290809993/500000000000 : ℝ) (251290809997/500000000000 : ℝ) (251293774073/500000000000 : ℝ) (251293774077/500000000000 : ℝ) (502587548111/1000000000000 : ℝ) (12564688703/25000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17017/131072 : ℝ))) 4 (251293774073/500000000000 : ℝ) (251293774077/500000000000 : ℝ) (502587548111/1000000000000 : ℝ) (12564688703/25000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17017/131072 : ℝ))) 5 (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17017/131072 : ℝ))) 6 (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17017/131072 : ℝ))) 7 (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17017/131072 : ℝ)) hmem 8 (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17017/131072 : ℝ))) hcmem 8 (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17017/131072 : ℝ)) (991934822069/1000000000000 : ℝ) (991934822071/1000000000000 : ℝ) (15705860879/31250000000 : ℝ) (502587548137/1000000000000 : ℝ) (12435650019/15625000000 : ℝ) (795881601233/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1497_exp_lower
  have heNumeric : (513728777057/250000000000 : ℝ)/4 ≤ Real.exp (-2664239295557/4000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (513728777057/250000000000 : ℝ)/4 ≤ Real.exp ((2127/16384 : ℝ)-(795881601233/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (2127/16384 : ℝ) (17017/131072 : ℝ) (795881601233/1000000000000 : ℝ) (513728777057/250000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1498; no trusted numerical premise.
theorem cover8_leaf1498_exp_radius : (49898667636944589/50000000000000000 : ℝ) ≤ Real.exp ((-8509/524288 : ℝ)/8) ∧ Real.exp ((-8509/524288 : ℝ)/8) ≤ (997973352738891781/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-8509/524288 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1498_exp_lower : (115014277191004539/125000000000000000 : ℝ) ≤ Real.exp ((-21313911592439/32000000000000 : ℝ)/8) ∧ Real.exp ((-21313911592439/32000000000000 : ℝ)/8) ≤ (920114217528036313/1000000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-21313911592439/32000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1498_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054915286237/1000000000000 : ℝ) ≤ 4*Real.exp (17017/131072 : ℝ)*Real.exp (-mu (radius 8 (8509/65536 : ℝ))) ∧ (20549/10000 : ℝ) < (2054915286237/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (8509/65536 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1498_exp_radius
  have hrNumeric : (491950680659/500000000000 : ℝ) ≤ Real.exp (-8509/524288 : ℝ) ∧ Real.exp (-8509/524288 : ℝ) ≤ (983901361319/1000000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (491950680659/500000000000 : ℝ) ≤ (radius 8 (8509/65536 : ℝ)) ∧ (radius 8 (8509/65536 : ℝ)) ≤ (983901361319/1000000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (8509/65536 : ℝ)) (491950680659/500000000000 : ℝ) (983901361319/1000000000000 : ℝ) (17871237001/100000000000 : ℝ) (5584761563/31250000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (8509/65536 : ℝ)) (491950680659/500000000000 : ℝ) (983901361319/1000000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (8509/65536 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (491950680659/500000000000 : ℝ) (983901361319/1000000000000 : ℝ) (991950680659/1000000000000 : ℝ) (49597534033/50000000000 : ℝ) (99191802147/100000000000 : ℝ) (30997438171/31250000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (8509/65536 : ℝ)) 1 (991950680659/1000000000000 : ℝ) (49597534033/50000000000 : ℝ) (99191802147/100000000000 : ℝ) (30997438171/31250000000 : ℝ) (123991793883/125000000000 : ℝ) (495967175533/500000000000 : ℝ) (99193435093/100000000000 : ℝ) (247983587733/250000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (8509/65536 : ℝ)) 2 (123991793883/125000000000 : ℝ) (495967175533/500000000000 : ℝ) (99193435093/100000000000 : ℝ) (247983587733/250000000000 : ℝ) (991934350997/1000000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (8509/65536 : ℝ)) 3 (991934350997/1000000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (8509/65536 : ℝ)) 4 (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (8509/65536 : ℝ)) 5 (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (8509/65536 : ℝ)) 6 (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (8509/65536 : ℝ)) 7 (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (8509/65536 : ℝ))) (17871237001/100000000000 : ℝ) (5584761563/31250000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (8509/65536 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (17871237001/100000000000 : ℝ) (5584761563/31250000000 : ℝ) (117871237001/200000000000 : ℝ) (36834761563/62500000000 : ℝ) (42274385863/100000000000 : ℝ) (211371929319/500000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (8509/65536 : ℝ))) 1 (117871237001/200000000000 : ℝ) (36834761563/62500000000 : ℝ) (42274385863/100000000000 : ℝ) (211371929319/500000000000 : ℝ) (506050021817/1000000000000 : ℝ) (506050021823/1000000000000 : ℝ) (499145978403/1000000000000 : ℝ) (49914597841/100000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (8509/65536 : ℝ))) 2 (506050021817/1000000000000 : ℝ) (506050021823/1000000000000 : ℝ) (499145978403/1000000000000 : ℝ) (49914597841/100000000000 : ℝ) (50259800011/100000000000 : ℝ) (502598000117/1000000000000 : ℝ) (251293072557/500000000000 : ℝ) (502586145121/1000000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (8509/65536 : ℝ))) 3 (50259800011/100000000000 : ℝ) (502598000117/1000000000000 : ℝ) (251293072557/500000000000 : ℝ) (502586145121/1000000000000 : ℝ) (125648018153/250000000000 : ℝ) (502592072619/1000000000000 : ℝ) (502592072577/1000000000000 : ℝ) (100518414517/200000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (8509/65536 : ℝ))) 4 (125648018153/250000000000 : ℝ) (502592072619/1000000000000 : ℝ) (502592072577/1000000000000 : ℝ) (100518414517/200000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (8509/65536 : ℝ))) 5 (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (8509/65536 : ℝ))) 6 (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (8509/65536 : ℝ))) 7 (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (8509/65536 : ℝ)) hmem 8 (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (8509/65536 : ℝ))) hcmem 8 (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (8509/65536 : ℝ)) (247983587749/250000000000 : ℝ) (991934350999/1000000000000 : ℝ) (251296036297/500000000000 : ℝ) (251296036301/500000000000 : ℝ) (159177828797/200000000000 : ℝ) (397944572001/500000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1498_exp_lower
  have heNumeric : (2054915286237/1000000000000 : ℝ)/4 ≤ Real.exp (-21313911592439/32000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054915286237/1000000000000 : ℝ)/4 ≤ Real.exp ((17017/131072 : ℝ)-(397944572001/500000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (17017/131072 : ℝ) (8509/65536 : ℝ) (397944572001/500000000000 : ℝ) (2054915286237/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

-- Proposed record cover8_leaf1499; no trusted numerical premise.
theorem cover8_leaf1499_exp_radius : (997973233771204501/1000000000000000000 : ℝ) ≤ Real.exp ((-17019/1048576 : ℝ)/8) ∧ Real.exp ((-17019/1048576 : ℝ)/8) ≤ (498986616885602251/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-17019/1048576 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1499_exp_lower : (920114227525713513/1000000000000000000 : ℝ) ≤ Real.exp ((-10656954405411/16000000000000 : ℝ)/8) ∧ Real.exp ((-10656954405411/16000000000000 : ℝ)/8) ≤ (460057113762856757/500000000000000000 : ℝ) := by
  have h := exp_small_bounds ((-10656954405411/16000000000000 : ℝ)/8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h ⊢
  constructor <;> linarith
theorem cover8_leaf1499_certificate
    (hidentity : ∀ modulus ∈ Ioo (0 : ℝ) 1, ellipticK modulus = Real.pi/(2*agm (complement modulus))) :
    (2054915464861/1000000000000 : ℝ) ≤ 4*Real.exp (8509/65536 : ℝ)*Real.exp (-mu (radius 8 (17019/131072 : ℝ))) ∧ (20549/10000 : ℝ) < (2054915464861/1000000000000 : ℝ) := by
  have hmem := radius_mem 8 (by norm_num) (17019/131072 : ℝ) (by norm_num)
  have hcmem := complement_mem _ hmem
  have hr0 := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1499_exp_radius
  have hrNumeric : (983900422997/1000000000000 : ℝ) ≤ Real.exp (-17019/1048576 : ℝ) ∧ Real.exp (-17019/1048576 : ℝ) ≤ (491950211499/500000000000 : ℝ) :=
    ⟨le_trans (by norm_num) hr0.1, hr0.2.trans (by norm_num)⟩
  have hr : (983900422997/1000000000000 : ℝ) ≤ (radius 8 (17019/131072 : ℝ)) ∧ (radius 8 (17019/131072 : ℝ)) ≤ (491950211499/500000000000 : ℝ) := by
    convert hrNumeric using 1 <;> norm_num [radius]
  have hc := complement_interval_of_radius (radius 8 (17019/131072 : ℝ)) (983900422997/1000000000000 : ℝ) (491950211499/500000000000 : ℝ) (178717535861/1000000000000 : ℝ) (178717535867/1000000000000 : ℝ)
    hmem hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_0 := agm_interval_zero (radius 8 (17019/131072 : ℝ)) (983900422997/1000000000000 : ℝ) (491950211499/500000000000 : ℝ) hr
  have r_1 := agm_interval_step (radius 8 (17019/131072 : ℝ)) 0 (1/1 : ℝ) (1/1 : ℝ) (983900422997/1000000000000 : ℝ) (491950211499/500000000000 : ℝ) (495975105749/500000000000 : ℝ) (991950211499/1000000000000 : ℝ) (991917548487/1000000000000 : ℝ) (123989693561/125000000000 : ℝ)
    (by simpa only [div_one] using r_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_2 := agm_interval_step (radius 8 (17019/131072 : ℝ)) 1 (495975105749/500000000000 : ℝ) (991950211499/1000000000000 : ℝ) (991917548487/1000000000000 : ℝ) (123989693561/125000000000 : ℝ) (123991734999/125000000000 : ℝ) (495966939997/500000000000 : ℝ) (495966939929/500000000000 : ℝ) (49596693993/50000000000 : ℝ)
    r_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_3 := agm_interval_step (radius 8 (17019/131072 : ℝ)) 2 (123991734999/125000000000 : ℝ) (495966939997/500000000000 : ℝ) (495966939929/500000000000 : ℝ) (49596693993/50000000000 : ℝ) (39677355197/40000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ)
    r_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_4 := agm_interval_step (radius 8 (17019/131072 : ℝ)) 3 (39677355197/40000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ)
    r_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_5 := agm_interval_step (radius 8 (17019/131072 : ℝ)) 4 (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ)
    r_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_6 := agm_interval_step (radius 8 (17019/131072 : ℝ)) 5 (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ)
    r_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_7 := agm_interval_step (radius 8 (17019/131072 : ℝ)) 6 (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ)
    r_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have r_8 := agm_interval_step (radius 8 (17019/131072 : ℝ)) 7 (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ)
    r_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_0 := agm_interval_zero (complement (radius 8 (17019/131072 : ℝ))) (178717535861/1000000000000 : ℝ) (178717535867/1000000000000 : ℝ) hc
  have c_1 := agm_interval_step (complement (radius 8 (17019/131072 : ℝ))) 0 (1/1 : ℝ) (1/1 : ℝ) (178717535861/1000000000000 : ℝ) (178717535867/1000000000000 : ℝ) (58935876793/100000000000 : ℝ) (294679383967/500000000000 : ℝ) (422749968493/1000000000000 : ℝ) (422749968501/1000000000000 : ℝ)
    (by simpa only [div_one] using c_0) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_2 := agm_interval_step (complement (radius 8 (17019/131072 : ℝ))) 1 (58935876793/100000000000 : ℝ) (294679383967/500000000000 : ℝ) (422749968493/1000000000000 : ℝ) (422749968501/1000000000000 : ℝ) (506054368211/1000000000000 : ℝ) (253027184109/500000000000 : ℝ) (499150679227/1000000000000 : ℝ) (99830135847/200000000000 : ℝ)
    c_1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_3 := agm_interval_step (complement (radius 8 (17019/131072 : ℝ))) 2 (506054368211/1000000000000 : ℝ) (253027184109/500000000000 : ℝ) (499150679227/1000000000000 : ℝ) (99830135847/200000000000 : ℝ) (502602523719/1000000000000 : ℝ) (502602523727/1000000000000 : ℝ) (502590670047/1000000000000 : ℝ) (100518134011/200000000000 : ℝ)
    c_2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_4 := agm_interval_step (complement (radius 8 (17019/131072 : ℝ))) 3 (502602523719/1000000000000 : ℝ) (502602523727/1000000000000 : ℝ) (502590670047/1000000000000 : ℝ) (100518134011/200000000000 : ℝ) (502596596883/1000000000000 : ℝ) (502596596891/1000000000000 : ℝ) (31412287303/62500000000 : ℝ) (502596596857/1000000000000 : ℝ)
    c_3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_5 := agm_interval_step (complement (radius 8 (17019/131072 : ℝ))) 4 (502596596883/1000000000000 : ℝ) (502596596891/1000000000000 : ℝ) (31412287303/62500000000 : ℝ) (502596596857/1000000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ)
    c_4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_6 := agm_interval_step (complement (radius 8 (17019/131072 : ℝ))) 5 (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ)
    c_5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_7 := agm_interval_step (complement (radius 8 (17019/131072 : ℝ))) 6 (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ)
    c_6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have c_8 := agm_interval_step (complement (radius 8 (17019/131072 : ℝ))) 7 (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ)
    c_7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have har := agm_bounds_of_interval (radius 8 (17019/131072 : ℝ)) hmem 8 (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) r_8
  have hac := agm_bounds_of_interval (complement (radius 8 (17019/131072 : ℝ))) hcmem 8 (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) c_8
  have hmu := mu_interval_of_agm (radius 8 (17019/131072 : ℝ)) (247983469981/250000000000 : ℝ) (991933879927/1000000000000 : ℝ) (100519319373/200000000000 : ℝ) (251298298437/500000000000 : ℝ) (795896686453/1000000000000 : ℝ) (795896686471/1000000000000 : ℝ)
    hmem (agm_elliptic_identity_from_dlmf hidentity _ hmem).2 har hac
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have he := exp_bounds_from_eighth _ _ _ (by norm_num) cover8_leaf1499_exp_lower
  have heNumeric : (2054915464861/1000000000000 : ℝ)/4 ≤ Real.exp (-10656954405411/16000000000000 : ℝ) := le_trans (by norm_num) he.1
  have heBox : (2054915464861/1000000000000 : ℝ)/4 ≤ Real.exp ((8509/65536 : ℝ)-(795896686471/1000000000000 : ℝ)) := by
    convert heNumeric using 1 <;> norm_num
  constructor
  · exact box_endpoint_lower_of_mu_interval 8 (8509/65536 : ℝ) (17019/131072 : ℝ) (795896686471/1000000000000 : ℝ) (2054915464861/1000000000000 : ℝ) hmu.2 heBox
  · norm_num

end SmaleRate.Proofs

#check SmaleRate.Proofs.cover8_leaf1475_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1475_certificate
#check SmaleRate.Proofs.cover8_leaf1476_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1476_certificate
#check SmaleRate.Proofs.cover8_leaf1477_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1477_certificate
#check SmaleRate.Proofs.cover8_leaf1478_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1478_certificate
#check SmaleRate.Proofs.cover8_leaf1479_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1479_certificate
#check SmaleRate.Proofs.cover8_leaf1480_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1480_certificate
#check SmaleRate.Proofs.cover8_leaf1481_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1481_certificate
#check SmaleRate.Proofs.cover8_leaf1482_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1482_certificate
#check SmaleRate.Proofs.cover8_leaf1483_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1483_certificate
#check SmaleRate.Proofs.cover8_leaf1484_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1484_certificate
#check SmaleRate.Proofs.cover8_leaf1485_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1485_certificate
#check SmaleRate.Proofs.cover8_leaf1486_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1486_certificate
#check SmaleRate.Proofs.cover8_leaf1487_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1487_certificate
#check SmaleRate.Proofs.cover8_leaf1488_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1488_certificate
#check SmaleRate.Proofs.cover8_leaf1489_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1489_certificate
#check SmaleRate.Proofs.cover8_leaf1490_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1490_certificate
#check SmaleRate.Proofs.cover8_leaf1491_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1491_certificate
#check SmaleRate.Proofs.cover8_leaf1492_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1492_certificate
#check SmaleRate.Proofs.cover8_leaf1493_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1493_certificate
#check SmaleRate.Proofs.cover8_leaf1494_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1494_certificate
#check SmaleRate.Proofs.cover8_leaf1495_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1495_certificate
#check SmaleRate.Proofs.cover8_leaf1496_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1496_certificate
#check SmaleRate.Proofs.cover8_leaf1497_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1497_certificate
#check SmaleRate.Proofs.cover8_leaf1498_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1498_certificate
#check SmaleRate.Proofs.cover8_leaf1499_certificate
#print axioms SmaleRate.Proofs.cover8_leaf1499_certificate
